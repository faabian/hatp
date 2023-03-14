import tactic
import init.meta.expr

set_option pp.locals_full_names true
set_option pp.instantiate_mvars false


open tactic expr

meta def get_pi_mvars : expr → tactic (list expr × expr)
| (pi n bi d b)  :=
do mv ← mk_meta_var d,
   (mvs, b) ← get_pi_mvars (b.instantiate_var mv),
   pure (mv::mvs, b)
| e              := pure ([], e)

meta def generalize_to_mvars (e : expr) : tactic (list expr × expr) :=
do let (fn, args) := get_app_fn_args e,
  mvs ← mmap (λ a, infer_type a >>= mk_meta_var) args,
  pure $ (mvs, app_of_list fn mvs)
 

-- Rewrite get_pis with de Bruijn indices AND metavariables. Then we can unify
-- X(M_1, ..., M_k, c_1, ..., c_n)
-- with
-- X(N_1, ..., N_l, d_1, ..., d_m)
-- while keeping track of the corresponding pi binders.

-- meta def mp (f : expr) (g : expr) : tactic expr :=
-- do
--   tf ← infer_type f,
--   tg ← infer_type g,
--   (fmvs, fconc') ← get_pi_mvars tf, 
--   (flocs, fconc) ← mk_local_pis tf,
--   -- (mvs, gen) ← generalize_to_mvars fconc,
--   -- trace gen,
--   -- unify gen fconc',
--   -- trace gen,
--   pat ← mk_pattern [] flocs fconc [] flocs,
--   trace pat,
--   (glocs, gconc) ← mk_local_pis tg,
--   -- (gmvs, gconc') ← get_pi_mvars tf,
--   gtys ← mmap infer_type glocs, 
--   trace flocs,
--   trace glocs,
--   trace gtys,
--   matches ← mmap (λ ty, try_core $ match_pattern pat ty) gtys,
--   trace matches,
--   let args := list.zip glocs matches,
--   trace args,
--   let args' := list.map (λ (a : expr × option (list level × list expr)),
--   match a with
--   | (x, none) := x
--   | (_, some (us, hs)) := app_of_list f hs
--   end
--   ) args, 
--   trace args',
--   let vars := list.map prod.fst $ list.filter (λ (a : expr × option (list level × list expr)), option.is_none a.2) args,
--   let res := app_of_list g args',
--   let res := expr.lambdas vars res,
--   trace res,
--   infer_type res >>= trace,
--   pure res


-- Apply an hypothesis to fill in one argument in another hypothesis. If there are multiple matches, applies
-- the hypothesis once in each possible location.
-- Meant for skolemized propositions (forall props), but this is not enforced. 
-- meta def mp' (f g : expr) : tactic expr :=
-- do tf ← infer_type f,
--   tg ← infer_type g,
--   -- (glocs, gconc) ← mk_local_pis tg,
--   (gmvs, gconc) ← get_pi_mvars tg,
--   gtys ← mmap infer_type gmvs, 
--   matches ← mmap (λ t, do
--     (fmvs, fconc) ← get_pi_mvars tf,    -- fresh mvars each time
--     (gmvs, gconc) ← get_pi_mvars tg,
--     trace t,
--     trace fconc,
--     try_core $ (do unify fconc t, pure (t, fconc))
--    ) gtys,
--    trace matches,
--   --  let res := list.map (λ ) matches,
--    pure (var 0)


-- Replace assigned metavariables by their assigned values.
meta def replace_mvars :=
expr.traverse $ λ e,
do match is_mvar e with
| tt := do
  assigned ← is_assigned e,
  match assigned with
  | tt := get_assignment e
  | ff := pure e
  end
| ff := pure e
end



-- meta def mvar_lambdas : list expr → list expr → expr → tactic expr
-- | (local_const uniq pp info t :: es) (mvar _ _ _ :: ms) f := do
  
--   lam pp info t (abstract_local (lambdas es f) uniq)
-- | _ _ f := pure f


-- returns expr and its local variables
meta def mk_mvar_app_aux : expr → list expr → list expr → tactic (expr × list expr)
| g (m::ms) local_vars := do
  g ← replace_mvars g,
  (loc::locs, _) ← infer_type g >>= mk_local_pis,
  trace g,
  infer_type g >>= trace,
  trace (m, ms, loc, locs),
  assigned ← is_assigned m,
  match assigned with
  | tt := mk_mvar_app_aux (app g m) ms local_vars
  | ff := do
    tm ← infer_type m,
    tm ← replace_mvars tm,
    tloc ← infer_type loc,
    trace (loc, tm, tloc),
    unify tm tloc,
    unify m loc,
    trace (loc, tm, tloc),
    mk_mvar_app_aux (app g loc) ms (loc::local_vars)
  end
| g [] local_vars := pure (g, list.reverse local_vars)


meta def mk_mvar_app : expr → list expr → tactic (expr × list expr) :=
λ e ms, mk_mvar_app_aux e ms []



meta def mp_nth_arg (f g : expr) (n : ℕ) : tactic expr :=
do tf ← infer_type f,
  tg ← infer_type g,
  -- (glocs, gconc') ← mk_local_pis tg,
  (gmvs, gconc) ← get_pi_mvars tg,
  gtys ← mmap infer_type gmvs,
  let replace : list bool := list.map (= n) $ list.range (list.length gtys),
  trace replace,
  match list.nth gtys n with
  | some t := do
    (fmvs, fconc) ← get_pi_mvars tf,
    trace t,
    trace fconc,
    unify fconc t,
    trace t,
    trace fconc,
    mmap (λ m, try_core (get_assignment m) >>= trace) gmvs,

    -- args ← mmap (λ a, match a with
    -- | ((m, loc), ff) := do assigned ← is_assigned m, match assigned with
    --   | tt := do trace ("assigned", m), pure m --do m' ← replace_mvars m, trace m', pure m'
    --   | ff := do tm ← infer_type m, tm ← replace_mvars tm, tloc ← infer_type loc, trace (loc, tm, tloc), unify tm tloc, trace (loc, tm, tloc), pure loc
    --   end
    -- | (_, tt) := app_of_list f <$> (mmap replace_mvars fmvs)
    -- end   
    -- ) (list.zip (list.zip gmvs glocs) replace),
    -- trace args,
    -- let res := app_of_list g args,
    gmvs ← mmap (λ a, match a with
    | (m, tt) := do (app_of_list f <$> (mmap replace_mvars fmvs)) >>= unify m, trace m, pure m
    | (m, ff) := pure m    
    end
    ) (list.zip gmvs replace),
    (res, locs) ← mk_mvar_app g gmvs,
    trace (res, locs),
    let b := list.head locs,
    trace $ local_uniq_name b,
    trace (abstract_local res (local_uniq_name b)),
    trace $ expr.lambdas locs res,
    let res := expr.lambdas locs res,  
    replace_mvars res >>= trace,
    infer_type res >>= trace,
    pure res
   | none := failed
   end

meta def mp (f g : expr) : tactic (list (option expr)) :=
do tg ← infer_type g,
  let n := pi_arity tg,
  trace tg,
  trace n,
  res ← mmap (λ k, try_core $ mp_nth_arg f g k) (list.range n),
  trace res,
  pure res 




def P : ℕ → ℕ → Prop := sorry
def Q : ℕ → ℕ → ℕ → Prop := sorry
def R : ℕ → Prop := sorry 
def f : ∀ a, P a a := sorry
def g : ∀ a b c, P a b → P b c → Q a b c := sorry  

-- def P : ℕ → Prop := sorry
-- def Q : ℕ → Prop := sorry
-- def R : ℕ → Prop := sorry 
-- def f : ∀ a, P a := sorry
-- def g : ∀ a, P a → Q a → R a := sorry  


-- #eval mp' `(f) `(g)

#eval mp_nth_arg `(f) `(g) 3



meta def mwe (e : expr) : tactic unit :=
do (a::_, conc) ← infer_type e >>= mk_local_pis,
  trace a,
  trace conc,
  trace $ abstract_local conc (local_uniq_name a)

#eval mwe `(f)
  


