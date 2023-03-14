import init.meta.expr
import data.multiset.basic

-- Define a hole expression type in which holes can be annotated with hole expressions they have to contain or 
-- may nor contain. We directly generalize `expr`. For the moment, only annotate holes (`mvar`) and `app` to allow
-- `contains` to `or`-distribute over the children.

-- _ +(z, no x) (_ + _) = (_ + _) + _
-- linear_indepent _ i(S) -> linear_independent _ j(S)

-- _ = _(no x!!)

meta inductive gvar
/- A bound variable with a de-Bruijn index. -/
| var         (i : nat) : gvar
/- A type universe: `Sort u` -/
| sort        (l : level) : gvar
/- A global constant. These include definitions, constants and inductive type stuff present
in the environment as well as hard-coded definitions. -/
| const       (name : name) (ls : list level) : gvar
/- [WARNING] Do not trust the types for `mvar` and `local_const`,
they are sometimes dummy values. Use `tactic.infer_type` instead. -/
/- An `mvar` is a 'hole' yet to be filled in by the elaborator or tactic state. -/
| mvar        (unique : name) (pretty : name) (type : gvar) (contains : multiset gvar) (avoids : multiset gvar) : gvar
/- A local constant. For example, if our tactic state was `h : P ⊢ Q`, `h` would be a local constant. -/
| local_const (unique : name) (pretty : name) (bi : binder_info) (type : gvar) : gvar
/- Function application. -/
| app         (f : gvar) (x : gvar) (contains : multiset gvar) (avoids : multiset gvar) : gvar
/- Lambda abstraction. eg ```(λ a : α, x)`` -/
| lam         (var_name : name) (bi : binder_info) (var_type : gvar) (body : gvar) : gvar
/- Pi type constructor. eg ```(Π a : α, x)`` and ```(α → β)`` -/
| pi          (var_name : name) (bi : binder_info) (var_type : gvar) (body : gvar) : gvar
/- An explicit let binding. -/
| elet        (var_name : name) (type : gvar) (assignment : gvar) (body : gvar) : gvar
/- A macro, see the docstring for `macro_def`.
  The list of expressions are local constants and metavariables that the macro depends on.
  -/
| macro       (m : macro_def) (args : list expr) : gvar
-- with annotation : Type
-- | mk  : annotation


-- Forget annotations to obtain usual `expr`. What do we need to add to prove termination?
meta def to_expr : gvar -> expr
| (gvar.var i) := expr.var i
| (gvar.sort l) := expr.sort l
| (gvar.const nm ls) := expr.const nm ls
| (gvar.mvar unm nm ty _ _) := expr.mvar unm nm (to_expr ty)
| (gvar.local_const unm nm bi ty) := expr.local_const unm nm bi (to_expr ty)
| (gvar.app f x _ _) := expr.app (to_expr f) (to_expr x)
| (gvar.lam nm bi ty body) := expr.lam nm bi (to_expr ty) (to_expr body)
| (gvar.pi nm bi ty body) := expr.pi nm bi (to_expr ty) (to_expr body)
| (gvar.elet nm ty val body) := expr.elet nm (to_expr ty) (to_expr val) (to_expr body)
| (gvar.macro m args) := expr.macro m args


-- Unification procedure.

-- Idea: use Lean's (higher-order) `unify` on the corresponding `expr`s. Then check whether the `mvar` assignments
-- respected the `contains` and `avoids` requirements. `avoids` should `and`-distribute to children, `contains` should
-- `or`-distribute. We will first implement a naive recursive version that propagates all conditions of the given
-- level downward, then recurses to deeper levels. The HO unification procedure could in principle be swapped.

-- TODO:
-- Lean 3 vs Lean 4
-- Access to unify internals?
-- quantified MP?

-- string bool name nat int syntax
-- mdata: name
-- hashmap: name → annotation

-- quantified MP forward
example (P Q : ℕ → Prop )(h : ∀ a b c : ℕ, P c) (hh : ∀ a b c : ℕ, P c → Q c) : 
  ∀ a b c : ℕ, Q c :=
λ a b c, hh a b c (h a b c)

-- quantified MT forward
example (P Q R : ℕ → Prop )(h : ∀ a b c : ℕ, P c → Q c) (hh : ∀ a b c : ℕ, Q c → R c) : 
  ∀ a b c : ℕ, P c → R c :=
λ a b c hp, hh a b c (h a b c hp)

-- quantified MP backward
example (P Q : ℕ → Prop ) (hh : ∀ a b c : ℕ, P c → Q c) : 
  ∀ a b c : ℕ, Q c :=
begin
  intros,
  apply hh,
  rotate 2,
  revert a b c,
  repeat {sorry}
end

-- quantified MT backward
example (P Q R : ℕ → Prop ) (hh : ∀ a b c : ℕ, Q c → R c) : 
  ∀ a b c : ℕ, P c → R c :=
begin
  intros a b c hq,
  apply hh,
  rotate 2,
  revert a b c,
  repeat {sorry}
end