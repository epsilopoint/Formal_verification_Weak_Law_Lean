/-
Copyright (c) 2022/09 Daniil Homza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Homza
-/
import probability.variance
--import probability.notation ???
/-!
# The Weak law of Large number 

We prove the `Weak Law of Large number`. The proof is well-known and
based on Chebyshev Inequality

(meas_ge_le_variance_div_sq in probability.variance)

ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2)

Proof will be consist of calculating of expected value 
and variance of (∑ i in range m, X i) and appling Chebyshev inequality 
in that case. 

We proof that for sequencese of random variable with 
𝔼[X_i]=𝔼[X_j], Var[X_i]=Var[X_j] we have 

* `exp_sum` : expected value of a sum `𝔼[(∑ i in range m, X i)] = m*𝔼[(X 0)]`
* `var_sum`: variance of a sum of independent r.v. `Var[(∑ i in range m, X i)] = m*Var[(X 0)]`
* `weak_law`: Weak Law of Large number
`tendsto (λ (n : ℕ), ℙ {ω | c*n ≤|(∑ i in range n, X i ) ω - n*𝔼[(X 0)]|}) at_top (𝓝 0)`

Note that Weak_Law has no assumption on identical distribution of `X i`.

## Implementation

We follow the proof by book 
Oliver C. Ibe,
in Fundamentals of Applied Probability and Random Processes (Second Edition), 2014
Proposition 6.1.


### Usefull definition


`ℙ - \ bp` - probability measure (probability)
`𝔼 - \ bbE` - Expected value 
`∀ = \ forall` - for all
`∃ - \ ex` - exists
`λ = \ la` - lambda (lambda calculus)
`ℕ = \ Nat` - natural number(include 0)
`ω = \ om` - omega, member of probability space(event)
`𝓝 = \ nhds` - neighborhoods (in topological space)
-/

open measure_theory filter finset 

noncomputable theory

open_locale topological_space big_operators probability_theory

-- topological space is responsible to nieghborhoods in weak_law theorem 

-- big operators is responsible to sum

/- ennreal The extended nonnegative real numbers. This is usually denoted [0, ∞],
 and is relevant as the codomain of a measure. -/

/- nnreal In this file we define nnreal (notation: ℝ≥0) 
 to be the type of non-negative real numbers, a.k.a. the interval [0, ∞) -/

namespace probability_theory


variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]{ω:Ω}{c:ℝ}


/-- Chebyshev inequality can be aplpied for sum of random variables with appropriate
expected value and variance  -/

lemma sum_cheb {X : ℕ → Ω → ℝ} 
(hint : ∀ i, integrable (X i)) (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
(same_exp: ∀ (m:ℕ), 𝔼[(X m)] = 𝔼[(X 0)]) (same_var: ∀ (m:ℕ), Var[(X m)]=Var[(X 0)]) 
(hs : ∀ i, mem_ℒp (X i) 2) (hc : 0 < c):
 ∀ (m:ℕ), (m>0) -> (ℙ {ω | c*m ≤ |(∑ i in range m, X i ) ω - m*𝔼[(X 0)]|}) ≤ ennreal.of_real (Var[(X 0)] / (c^2*m)):=
begin
  have exp_sum: ∀ (m:ℕ), 𝔼[(∑ i in range m, X i)] = m*𝔼[(X 0)],
    begin

    have sum_exp: ∀ (m:ℕ), 𝔼[(∑ i in range m, X i)] = ∑ i in range m, 𝔼[(X i)],
      begin
      intro m,
      simp[integral_finset_sum, hint],
      end,
    intro m,
    rw sum_exp,
    simp only[same_exp],
    simp,
    end,

  have var_sum: ∀ cl(m:ℕ), Var[(∑ i in range m, X i)] = m*Var[(X 0)],
    begin

    have sum_var: ∀ (m:ℕ), Var[(∑ i in range m, X i)] = ∑ i in range m, Var[(X i)],
      begin
      intro m,
      rw indep_fun.variance_sum,
      intros i im,
      specialize hs i,
      exact hs,
      intros i j p pr prn,
      specialize hindep i p prn,
      exact hindep,
      end,
    intro m,
    simp[sum_var,same_var],
    end,

  have simplif_eq: ∀ (m:ℕ), (m>0) -> ennreal.of_real (Var[(X 0)] / (c^2*m))=ennreal.of_real((Var[(X 0)]* m) / (c*m) ^ 2):=
    begin
    intros m mp,
    rw [← div_inv_eq_mul Var[X 0], div_div],
    congrm ennreal.of_real (Var[X 0] / _),
    ring_nf,
    congrm (_*c^2),
    rw ← div_eq_inv_mul,
    rw pow_two,
    simp[mul_div_cancel'''],
    end,
  have int2: ∀ (m:ℕ), mem_ℒp (∑ i in range m, X i ) 2,
    intro m,
    ring_nf,
    refine mem_ℒp_finset_sum' (range m) _,
    intros i ip,
    specialize hs i,
    exact hs,

  have ineq: ∀ (m:ℕ), (m>0) -> (ℙ {ω | c*m ≤ |(∑ i in range m, X i ) ω - m*𝔼[(X 0)]|}) ≤ ennreal.of_real (Var[(∑ i in range m, X i)] / (c*m) ^ 2),
    begin
    intros m mp,
    have C: ∀ (m:ℕ), (m>0) -> 0<c*m,
      intros m mp,
      simp[hc, mp],
      exact mp,
      specialize C m mp,
      specialize exp_sum m,
      rw ← exp_sum,
      specialize int2 m,
      apply meas_ge_le_variance_div_sq,
      exact int2,
      exact C,
    end,

  have B: ∀ (m:ℕ), Var[(∑ i in range m, X i)] = Var[(X 0)]*m,
    begin
    intro m,
    specialize var_sum m,
    rw var_sum,
   finish,
    end,
  intros m mp,
  specialize var_sum m,
  specialize ineq m mp,
  specialize simplif_eq m mp,
    specialize B m,
  rw simplif_eq,
  rw ← B,
  exact ineq,
end


theorem weak_law {X : ℕ → Ω → ℝ} 
(hint : ∀ i, integrable (X i)) (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
(same_exp: ∀ (m:ℕ), 𝔼[(X m)] = 𝔼[(X 0)]) (same_var: ∀ (m:ℕ), Var[(X m)]=Var[(X 0)]) 
(hs : ∀ i, mem_ℒp (X i) 2)(hc : 0 < c): 
tendsto (λ (n : ℕ), ℙ {ω | c*n ≤|(∑ i in range n, X i ) ω - n*𝔼[(X 0)]|}) at_top (𝓝 0) :=
begin

rw ennreal.tendsto_at_top_zero,
intros e e_pos,
let N:= nat.ceil(Var[(X 0)]/(c^2*(ennreal.to_real(e)))),

have A: let N := ⌈Var[X 0] / (c ^ 2 * e.to_real)⌉₊ in ∀ (n: ℕ) (n_pos : n ≥ N),
    ennreal.of_real (Var[(X 0)]/(c^2*n)) ≤ e :=
begin
  intros N n hn,
  -- annoying special case n = 0
  rcases nat.eq_zero_or_pos n with (rfl | hn0), { simp, },
  -- annoying special case e    = ∞
  rcases eq_top_or_lt_top e with (rfl | he), { simp, },
  -- using N just makes things more annoying. Why not just not define N at all?
  change ⌈ _ ⌉₊ ≤ n at hn,
  -- get rid of ceiling
  rw nat.ceil_le at hn,
  -- get rid of ennreal stuff in goal
  apply ennreal.of_real_le_of_le_to_real,
  -- clear denominators (will show they're positive later)
  rw div_le_iff at hn ⊢,
  { -- main goal now easy
    convert hn using 1,
    ring, },
  { -- positivity side goal: a bit annoying that I need to use theorems and not tactics here
    exact mul_pos (pow_pos hc 2) (by exact_mod_cast hn0), },
  { -- second positivity side goal: here we still have to deal with e
    refine mul_pos (pow_pos hc 2) _,
    rw ennreal.to_real_pos_iff,
    exact ⟨e_pos, he⟩, },
end,


have sum_cheb1: ∀ (n:ℕ), (n>0) -> (ℙ {ω | c*n ≤ |(∑ i in range n, X i ) ω - n*𝔼[(X 0)]|}) ≤ ennreal.of_real (Var[(X 0)] / (c^2*n)):=
begin
  exact (sum_cheb hint hindep same_exp same_var hs hc),
end,
rcases nat.eq_zero_or_pos N with h1 | h2,
use 1,
intros n n1,
have n0: n>0,
  simp[n1],
  rcases nat.eq_zero_or_pos n with q1 | q2,
  exfalso,
  rw q1 at n1,
  finish using n1,
  exact q2,
  specialize sum_cheb1 n n0,
  apply le_trans sum_cheb1,
  have t0: n≥N,
  rw h1,
  simp[n0],
  specialize A n t0,
  exact A,
  use N,
  intros n nbigN,
  have n0: n>0,
  rcases nat.eq_zero_or_pos n with s1 | s2,
  exfalso,
  rw s1 at nbigN,
  have r0: 0<0,
  exact (lt_of_lt_of_le h2 nbigN),
  finish using r0,
  exact s2,
  specialize sum_cheb1 n n0,
  apply le_trans sum_cheb1,
  specialize A n nbigN,
  exact A,


end
end probability_theory