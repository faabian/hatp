import topology.basic
import data.real.basic
import topology.metric_space.basic
import topology.uniform_space.uniform_convergence
import topology.uniform_space.basic



-- set_option pp.all true

open filter

theorem unif_cont 
  (F : ℕ → ℝ → ℝ) (hF : ∀ n, continuous (F n))
  (f : ℝ → ℝ) (hFf : tendsto_uniformly F f at_top) :
  continuous f :=
begin
  -- set up fully "peeled" proof state:
  rw metric.continuous_iff,    -- metric def of continuity
  intros x ε hε,    -- introduce universally quantified variables into the proof state

  -- solution to disallowed metavarible dependencies: skolimize and rcases first!
  simp [metric.continuous_iff] at hF,    -- metric definition of continuity
  simp [classical.skolem] at hF,
  -- sometimes with skolem behind other universal quantifiers, you need to help Lean a bit
  -- (simp and rw don't work)
  -- rw [classical.skolem] at hF,    -- try yourself
  -- simp [classical.skolem] at hF,  -- try yourself
  have hF := λ n b, classical.skolem.mp (hF n b),
  have hF' := λ n, classical.skolem.mp (hF n),
  simp [classical.skolem] at hF',
  clear hF,
  clear hF,
  rcases hF' with ⟨δ, hF⟩,
  have hδ := λ n x ε hε, and.elim_left (hF n x ε hε),
  have hF := λ n x ε hε, and.elim_right (hF n x ε hε),

  -- the same for the other hypothesis
  rw metric.tendsto_uniformly_iff at hFf,
  simp at hFf,    -- get rid of `at_top`
  simp [classical.skolem] at hFf,
  rcases hFf with ⟨M, hM⟩,  

  apply exists.intro,    -- delay choice, creates mvars
  apply exists.intro,    -- delay choice, creates mvars
  rotate 1,    -- postpone a goal by rotating the goal list
  intros y hxy,

  -- start the proof
  apply lt_of_le_of_lt,    -- transitivity
  apply dist_triangle,     -- triangle inequality
  rotate 1,
  apply lt_of_lt_of_le,
  apply add_lt_add_left,    -- bound a summand
  rw dist_comm,    -- symmetry
  apply hM,    -- apply the hypothesis
  
  rotate 4,
  apply le_trans,
  apply add_le_of_add_le_right,
  rotate 1,
  apply dist_triangle,
  rotate 9,
  -- apply le_trans,
  apply add_le_of_add_le_right,
  rotate 1,
  apply add_le_of_add_le_right,
  rotate 1,
  apply le_of_lt,
  apply hM,
  rotate 14,
  apply add_le_of_add_le_left,
  rotate 1,
  have hF' := hF _,    -- apply the hypothesis to an argument to be specified later
  apply le_of_lt,
  apply hF',

  -- supply all the epsilons
  rotate 2,
  use ε / 3,
  apply le_refl,
  rotate 1,
  use ε / 3,
  rotate 2,
  rotate 1,
  -- use ε,
  use δ (M (ε / 3) (by linarith)) x (ε / 3) (by linarith),  -- now we can supply "the" delta belonging to "the" M
  rotate 1,
  apply le_refl,
  apply le_of_eq,
  apply add_eq_of_eq_sub,
  refl,
  apply le_of_eq,
  apply eq_sub_of_add_eq,
  ring_nf,
  exact hxy,
  apply le_refl,
  apply hδ,
end



-- Toy example for this sort of behavior:
-- if we defer the choice of `y` at the very beginning,
-- the goal cannot be closed with `hx`
-- because it would assign `x` to the second goal which (syntactically) is not allowed.
-- But above we **need** to delay the choice of `δ` early so that we can continue to unpack and work with the goal.
theorem test (h : ∃ x, x = 0) : ∃ y, y = 0 :=
begin
  -- apply exists.intro,    -- uncomment
  rcases h with ⟨x, hx⟩,
  apply exists.intro,    -- comment
  exact hx,
end