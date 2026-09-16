import Submission.ZagierHoffmanProof.StepL3

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L4: §2.2 operator calculus — the B* maps (paper Prop 2.5, Cor 2.6, Cor 2.7)

A *binary relation* `R` of the paper is `Σ_i a_i·S_d(s_i) + Σ_j b_j·S_{d+1}(t_j) = 0`
holding for every level `d`.  `Rlevel(j)` below is its level-`j` value.  The Todd
operator `B*_v` multiplies `S_d(v)` into the partial sum of `R` over levels `< d`:

  B*_v(R)(d) := S_d(v)·Σ_{j<d} R(j) = 0,

which by the recursion `S_d(v::s) = S_d(v)·S_<d(s)` expands (paper Prop 2.5) to
`Σ_i a_i S_d(v,s_i) + Σ_j b_j S_d(v,t_j) + Σ_j b_j S_d(v)·S_d(t_j) = 0`.  Over the
natural levels (rather than the paper's ℤ) the shift `Σ_{j<d} S_{j+1}(t)` telescopes to
`S_<d(t) + S_d(t)` only when `S_0(t) = 0`, i.e. when every b-tuple has depth ≥ 2 —
exactly the situation of all relations produced in §2.3 (Lemma-2.9 outputs and their
`(1 :: …)` descendants).  `bstar` records Prop 2.5 in that form; `bstar_pure` is
Cor 2.7 (pure first-slot merge via `S_mul_P_pure`, paper requires `v + t₁ ≤ q`);
Cor 2.6 (fixed relations) is already `StepL1.fixed_rel_prepend`.  All sorry-free.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma sum_shift_succ {r : ℕ} (hr : 0 < r) (hr2 : 1 < r) (c : Fin r → ℕ+) (d : ℕ) :
    (∑ j ∈ Finset.range d, S F r hr c (j + 1)) = S_lt F r hr c (d + 1) := by
  classical
  rw [S_lt_eq_sum_levels F r hr c (d + 1)]
  have hre := Finset.sum_range_succ' (n := d) (f := fun e : ℕ => S F r hr c e)
  rw [hre]
  rw [S_zero_of_depth_ge_two F hr hr2 c]
  simp

noncomputable def Rlevel {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    (j : ℕ) : RatFunc.CompletionAtInfty F :=
  (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (depA i) (hdepA i) (cA i) j)) +
  (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
      S F (depB k) (hdepB k) (cB k) (j + 1)))

lemma bstar_algebra {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (hB2 : ∀ j, 1 < depB j) (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    (v : ℕ+) (d : ℕ) :
    P F d v * (∑ j ∈ Finset.range d, Rlevel F depA hdepA cA aA depB hdepB cB aB j) =
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (P F d v * S F (depB k) (hdepB k) (cB k) d))) := by
  classical
  let K := RatFunc.CompletionAtInfty F
  let gA : ι → K := fun i => ((aA i : RatFunc F) : K)
  let gB : κ → K := fun k => ((aB k : RatFunc F) : K)
  have hA : P F d v * (∑ j ∈ Finset.range d, (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) j)) =
      ∑ i : ι, gA i * S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d := by
    calc
      P F d v * (∑ j ∈ Finset.range d, (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) j))
          = P F d v * (∑ i : ι, (∑ j ∈ Finset.range d, gA i * S F (depA i) (hdepA i) (cA i) j)) := by
            rw [Finset.sum_comm]
      _ = P F d v * (∑ i : ι, gA i * (∑ j ∈ Finset.range d, S F (depA i) (hdepA i) (cA i) j)) := by
            apply congrArg (fun t : K => P F d v * t)
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
      _ = P F d v * (∑ i : ι, gA i * S_lt F (depA i) (hdepA i) (cA i) d) := by
            apply congrArg (fun t : K => P F d v * t)
            apply Finset.sum_congr rfl
            intro i hi
            rw [S_lt_eq_sum_levels F (depA i) (hdepA i) (cA i) d]
      _ = ∑ i : ι, gA i * (P F d v * S_lt F (depA i) (hdepA i) (cA i) d) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ∑ i : ι, gA i * S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [S_prepend F d v (hdepA i) (cA i)]
  have hB : P F d v * (∑ j ∈ Finset.range d, (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (j + 1))) =
      (∑ k : κ, gB k * S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d) +
      (∑ k : κ, gB k * (P F d v * S F (depB k) (hdepB k) (cB k) d)) := by
    calc
      P F d v * (∑ j ∈ Finset.range d, (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (j + 1)))
          = P F d v * (∑ k : κ, (∑ j ∈ Finset.range d, gB k * S F (depB k) (hdepB k) (cB k) (j + 1))) := by
            rw [Finset.sum_comm]
      _ = P F d v * (∑ k : κ, gB k * (∑ j ∈ Finset.range d, S F (depB k) (hdepB k) (cB k) (j + 1))) := by
            apply congrArg (fun t : K => P F d v * t)
            apply Finset.sum_congr rfl
            intro k hk
            rw [← Finset.mul_sum]
      _ = P F d v * (∑ k : κ, gB k * S_lt F (depB k) (hdepB k) (cB k) (d + 1)) := by
            apply congrArg (fun t : K => P F d v * t)
            apply Finset.sum_congr rfl
            intro k hk
            rw [sum_shift_succ F (hdepB k) (hB2 k) (cB k) d]
      _ = ∑ k : κ, gB k * (P F d v * S_lt F (depB k) (hdepB k) (cB k) (d + 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (∑ k : κ, gB k * S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d) +
          (∑ k : κ, gB k * (P F d v * S F (depB k) (hdepB k) (cB k) d)) := by
            calc
              (∑ k : κ, gB k * (P F d v * S_lt F (depB k) (hdepB k) (cB k) (d + 1)))
                  = ∑ k : κ, gB k * (S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d +
                      (P F d v * S F (depB k) (hdepB k) (cB k) d)) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    rw [S_lt_succ F (depB k) (hdepB k) (cB k) d]
                    rw [mul_add]
                    rw [S_prepend F d v (hdepB k) (cB k)]
              _ = (∑ k : κ, gB k * S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d) +
                  (∑ k : κ, gB k * (P F d v * S F (depB k) (hdepB k) (cB k) d)) := by
                    calc
                      (∑ k : κ, gB k * (S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d +
                          (P F d v * S F (depB k) (hdepB k) (cB k) d)))
                          = ∑ k : κ, (gB k * S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d +
                              gB k * (P F d v * S F (depB k) (hdepB k) (cB k) d)) := by
                            apply Finset.sum_congr rfl
                            intro k hk
                            ring
                      _ = (∑ k : κ, gB k * S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d) +
                          (∑ k : κ, gB k * (P F d v * S F (depB k) (hdepB k) (cB k) d)) := by
                            rw [Finset.sum_add_distrib]
  calc
    P F d v * (∑ j ∈ Finset.range d, Rlevel F depA hdepA cA aA depB hdepB cB aB j)
        = P F d v * (∑ j ∈ Finset.range d,
            ((∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) j) +
             (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (j + 1)))) := by
          rfl
    _ = P F d v * ((∑ j ∈ Finset.range d, (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) j)) +
        (∑ j ∈ Finset.range d, (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (j + 1)))) := by
          rw [Finset.sum_add_distrib]
    _ = P F d v * (∑ j ∈ Finset.range d, (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) j)) +
        P F d v * (∑ j ∈ Finset.range d, (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (j + 1))) := by
          rw [mul_add]
    _ = (∑ i : ι, gA i * S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d) +
        ((∑ k : κ, gB k * S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d) +
        (∑ k : κ, gB k * (P F d v * S F (depB k) (hdepB k) (cB k) d))) := by
          rw [hA, hB]
    _ = (∑ i : ι, (((aA i : RatFunc F) : K) *
          S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d)) +
        (∑ k : κ, (((aB k : RatFunc F) : K) *
          S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d)) +
        (∑ k : κ, (((aB k : RatFunc F) : K) *
          (P F d v * S F (depB k) (hdepB k) (cB k) d))) := by
          dsimp [gA, gB]
          ac_rfl


/-- ★ Prop 2.5 (B*_v, ℕ-version): a valid binary relation R (a-terms at level e,
b-terms at level e+1, all b-tuples of depth ≥ 2) yields, for every v and every d,
`Σ a_i S_d(v,s_i) + Σ b_j S_d(v,t_j) + Σ b_j P_d(v)·S_d(t_j) = 0`. -/
theorem bstar {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (hB2 : ∀ j, 1 < depB j) (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    (v : ℕ+)
    (hR : ∀ e : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) e)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (e + 1))) = 0) :
    ∀ d : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (P F d v * S F (depB k) (hdepB k) (cB k) d))) = 0 := by
  classical
  intro d
  rw [← bstar_algebra F depA hdepA cA aA depB hdepB hB2 cB aB v d]
  have hsum0 : (∑ j ∈ Finset.range d, Rlevel F depA hdepA cA aA depB hdepB cB aB j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simpa [Rlevel] using (hR j)
  rw [hsum0]
  simp



/-- ★ Cor 2.7 (B*_v pure): when `v + (t_j)₁ ≤ q` for every b-tuple, the pure products
`P_d(v)·S_d(t_j)` merge into the first slot of `t_j`: `Σ a_i S_d(v,s_i) +
Σ b_j S_d(v,t_j) + Σ b_j S_d(v+t_j1, t_j⁻) = 0`. -/
theorem bstar_pure {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (hB2 : ∀ j, 1 < depB j) (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    (v : ℕ+)
    (hR : ∀ e : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) e)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (e + 1))) = 0)
    (hv : ∀ k : κ, (v : ℕ) + ((cB k) ⟨0, hdepB k⟩ : ℕ) ≤ Nat.card F) :
    ∀ d : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) d)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) d)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (headAdd v (hdepB k) (cB k)) d)) = 0 := by
  classical
  intro d
  by_cases hd0 : d = 0
  · subst d
    -- every S_0-block of a depth-≥2 tuple vanishes, so all three sums are 0
    have h1 : (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec v (cA i)) 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hdi : 0 < depA i := hdepA i
      rw [S_zero_of_depth_ge_two F (by omega : 0 < depA i + 1) (by omega : 1 < depA i + 1)
        (consVec v (cA i))]
      simp
    have h2 : (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (depB k + 1) (by omega : 0 < depB k + 1) (consVec v (cB k)) 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hdk : 0 < depB k := hdepB k
      rw [S_zero_of_depth_ge_two F (by omega : 0 < depB k + 1) (by omega : 1 < depB k + 1)
        (consVec v (cB k))]
      simp
    have h3 : (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
        S F (depB k) (hdepB k) (headAdd v (hdepB k) (cB k)) 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [S_zero_of_depth_ge_two F (hdepB k) (hB2 k) (headAdd v (hdepB k) (cB k))]
      simp
    rw [h1, h2, h3]
    simp
  · have hb := bstar F depA hdepA cA aA depB hdepB hB2 cB aB v hR d
    have hthird : (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
        (P F d v * S F (depB k) (hdepB k) (cB k) d))) =
        (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (headAdd v (hdepB k) (cB k)) d)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [S_mul_P_pure F v (hdepB k) (cB k) d (by omega : 1 ≤ d) (hv k)]
    rw [hthird] at hb
    exact hb




-- CW algebra (Prop 2.8, product form): R(d)·S_<d+1(W) equals the three-part product sum,
-- where R(d) = ΣA(d) + ΣB(d+1).  No depth hypothesis needed on the tuples of R.
lemma CW_algebra {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    {r : ℕ} (hr : 0 < r) (W : Fin r → ℕ+) (d : ℕ) :
    ((∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) d)) +
     (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (d + 1)))) * S_lt F r hr W (d + 1) =
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) d) * S_lt F r hr W d) +
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) d) * S F r hr W d) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1)) := by
  classical
  let K := RatFunc.CompletionAtInfty F
  let gA : ι → K := fun i => ((aA i : RatFunc F) : K)
  let gB : κ → K := fun k => ((aB k : RatFunc F) : K)
  calc
    ((∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) d) +
     (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (d + 1))) * S_lt F r hr W (d + 1)
        = (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) d) * S_lt F r hr W (d + 1) +
          (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1) := by
          rw [add_mul]
    _ = (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) d) * (S_lt F r hr W d + S F r hr W d) +
          (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1) := by
          rw [S_lt_succ F r hr W d]
    _ = (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) d) * S_lt F r hr W d +
          (∑ i : ι, gA i * S F (depA i) (hdepA i) (cA i) d) * S F r hr W d +
          (∑ k : κ, gB k * S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1) := by
          rw [mul_add]
    _ = (∑ i : ι, (gA i * S F (depA i) (hdepA i) (cA i) d) * S_lt F r hr W d) +
          (∑ i : ι, (gA i * S F (depA i) (hdepA i) (cA i) d) * S F r hr W d) +
          (∑ k : κ, (gB k * S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1)) := by
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
    _ = (∑ i : ι, (((aA i : RatFunc F) : K) * S F (depA i) (hdepA i) (cA i) d) * S_lt F r hr W d) +
          (∑ i : ι, (((aA i : RatFunc F) : K) * S F (depA i) (hdepA i) (cA i) d) * S F r hr W d) +
          (∑ k : κ, (((aB k : RatFunc F) : K) * S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1)) := by
          dsimp [gA, gB]

/-- ★ Prop 2.8 (CW): a valid relation R, multiplied by S_<d+1(W), gives the product
relation `Σ_i a_i S_d(s_i)S_<d(W) + Σ_i a_i S_d(s_i)S_d(W) + Σ_i b_i S_{d+1}(t_i)S_<d+1(W) = 0`. -/
theorem CW {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    {r : ℕ} (hr : 0 < r) (W : Fin r → ℕ+)
    (hR : ∀ e : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) e)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (e + 1))) = 0) :
    ∀ d : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) d) * S_lt F r hr W d) +
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) d) * S F r hr W d) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (d + 1)) * S_lt F r hr W (d + 1)) = 0 := by
  classical
  intro d
  have hCW := CW_algebra F depA hdepA cA aA depB hdepB cB aB hr W d
  -- target: three-part = 0; hCW: RHS-three-part = LHS; and LHS = R(d)·S_lt = 0·S_lt via hR
  rw [← hCW]
  have hR0 : ((∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) d)) +
     (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (d + 1)))) = 0 := hR d
  rw [hR0]
  simp



/-- C_t(R1) expanded (the relation BC_q = Prop 2.10 subtracts): for any tuple `t` of
depth `r ≥ 1`, `S_d(q,t) + S_d(q)S_d(t) + D1·S_{d+1}(1)·(S_<d+1(q−1)·S_<d+1(t)) = 0`
for every `d` — i.e. `R1(d)·S_<d+1(t) = 0` expanded (paper Lemma 2.9 / Prop 2.8 with
`W = t`).  The first two terms telescope back to `S_d(q)·S_<d+1(t)` (`cw_first_split`)
and the whole left side is exactly `cw_r1_display`'s. -/
theorem C_R1_expanded {r : ℕ} (hr : 0 < r) (t : Fin r → ℕ+) : ∀ d : ℕ,
    S F (r + 1) (by omega : 0 < r + 1) (consVec (qExp F) t) d
      + P F d (qExp F) * S F r hr t d
      + D1c F * ((P F (d + 1) oneExp) *
          (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
            S_lt F r hr t (d + 1))) = 0 := by
  classical
  intro d
  rw [← cw_first_split F hr t d]
  exact cw_r1_display F hr t d



-- C-side weighted sum over the b-family, from C_R1_expanded per tuple
lemma C_sum_zero {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F) (d : ℕ) :
    (∑ j : κ, (((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
        (S F (depB j + 1) (by omega : 0 < depB j + 1) (consVec (qExp F) (cB j)) d
          + (P F d (qExp F) * S F (depB j) (hdepB j) (cB j) d
          + D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1))))))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  have hc := C_R1_expanded F (hdepB j) (cB j) d
  -- NOTE: plain `rw [hc]` can silently miss the (associativity-equal) occurrence inside
  -- the product; `congrArg` + `simpa [add_assoc]` on the inner sum is the robust close.
  calc
    ((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
        (S F (depB j + 1) (by omega : 0 < depB j + 1) (consVec (qExp F) (cB j)) d
          + (P F d (qExp F) * S F (depB j) (hdepB j) (cB j) d
          + D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1)))))
        = ((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) * 0 := by
          apply congrArg (fun t : RatFunc.CompletionAtInfty F =>
            ((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) * t)
          simpa [add_assoc] using hc
    _ = 0 := by simp

-- generic: (Σ g·X) + ((Σ g·Y) + (Σ g·Z)) = Σ g·(X + (Y+Z))
lemma sum_distrib3 {κ : Type} [Fintype κ] (g : κ → RatFunc.CompletionAtInfty F)
    (X Y Z : κ → RatFunc.CompletionAtInfty F) :
    (∑ j : κ, g j * X j) + ((∑ j : κ, g j * Y j) + (∑ j : κ, g j * Z j)) =
      ∑ j : κ, g j * (X j + (Y j + Z j)) := by
  classical
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- ★ BC_q (paper Prop 2.10): from a valid R (deep b-tuples) one gets, for every d,
`Σ_i a_i S_d(q,s_i) − Σ_j b_j D1·S_{d+1}(1)·(S_<d+1(q−1)·S_<d+1(t_j)) = 0`. -/
theorem BC_q {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (hB2 : ∀ j, 1 < depB j) (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    (hR : ∀ e : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) e)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (e + 1))) = 0) :
    ∀ d : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec (qExp F) (cA i)) d)) -
      (∑ j : κ, (((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1)))))) = 0 := by
  classical
  intro d
  let K := RatFunc.CompletionAtInfty F
  let gA : ι → K := fun i => ((aA i : RatFunc F) : K)
  let gB : κ → K := fun k => ((aB k : RatFunc F) : K)
  let A := ∑ i : ι, gA i * S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec (qExp F) (cA i)) d
  let B1 := ∑ j : κ, gB j * S F (depB j + 1) (by omega : 0 < depB j + 1) (consVec (qExp F) (cB j)) d
  let B2 := ∑ j : κ, gB j * (P F d (qExp F) * S F (depB j) (hdepB j) (cB j) d)
  let C := ∑ j : κ, gB j * (D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1))))
  have hBstar : A + (B1 + B2) = 0 := by
    have hb := bstar F depA hdepA cA aA depB hdepB hB2 cB aB (qExp F) hR d
    simpa [A, B1, B2, gA, gB, add_assoc] using hb
  have hCsum0 : (∑ j : κ, gB j * (S F (depB j + 1) (by omega : 0 < depB j + 1) (consVec (qExp F) (cB j)) d
          + (P F d (qExp F) * S F (depB j) (hdepB j) (cB j) d
          + D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1)))))) = 0 := by
    simpa [gB] using (C_sum_zero F depB hdepB cB aB d)
  have hB1B2C : B1 + (B2 + C) = 0 := by
    have hsp := sum_distrib3 F gB
        (fun j => S F (depB j + 1) (by omega : 0 < depB j + 1) (consVec (qExp F) (cB j)) d)
        (fun j => P F d (qExp F) * S F (depB j) (hdepB j) (cB j) d)
        (fun j => D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1))))
    dsimp [B1, B2, C]
    rw [hsp]
    exact hCsum0
  calc
    A - C = (A + (B1 + B2)) - (B1 + (B2 + C)) := by
          dsimp [A, B1, B2, C]
          ring
    _ = 0 - (B1 + (B2 + C)) := by rw [hBstar]
    _ = 0 := by rw [hB1B2C]; simp



-- per b-term: expand S_<d+1(q−1)·S_<d+1(t) via p2WpT and fold S_{d+1}(1)·S_<d+1(·)
lemma bterm_expand {r : ℕ} (hr : 0 < r) (t : Fin r → ℕ+) (a : RatFunc F) (d : ℕ) :
    ((a : RatFunc F) : RatFunc.CompletionAtInfty F) *
      (D1c F * ((P F (d + 1) oneExp) *
        (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
          S_lt F r hr t (d + 1)))) =
      ∑ e : (p2WpT F (qMinusExp F) hr t).ι,
        (((a : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (D1c F * (((p2WpT F (qMinusExp F) hr t).f e : ℤ) : RatFunc.CompletionAtInfty F))) *
          S F ((p2WpT F (qMinusExp F) hr t).dep e + 1)
            (by omega : 0 < (p2WpT F (qMinusExp F) hr t).dep e + 1)
            (consVec oneExp ((p2WpT F (qMinusExp F) hr t).c e)) (d + 1) := by
  classical
  let D := p2WpT F (qMinusExp F) hr t
  let ca : RatFunc.CompletionAtInfty F := ((a : RatFunc F) : RatFunc.CompletionAtInfty F)
  have h1 : ca * (D1c F * ((P F (d + 1) oneExp) *
        (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) * S_lt F r hr t (d + 1)))) =
      ca * (D1c F * ((P F (d + 1) oneExp) *
            (∑ e : D.ι, ((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1)))) := by
    rw [D.hid (d + 1)]
  have h2 : ca * (D1c F * ((P F (d + 1) oneExp) *
            (∑ e : D.ι, ((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1)))) =
      ∑ e : D.ι, (ca * (D1c F * (((D.f e : ℤ) : RatFunc.CompletionAtInfty F)))) *
          S F (D.dep e + 1) (by omega : 0 < D.dep e + 1) (consVec oneExp (D.c e)) (d + 1) := by
    calc
      ca * (D1c F * ((P F (d + 1) oneExp) *
            (∑ e : D.ι, ((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
              S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1))))
          = ca * (D1c F * (∑ e : D.ι, (P F (d + 1) oneExp) *
              (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
                S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1)))) := by
            rw [Finset.mul_sum]
      _ = ca * (∑ e : D.ι, D1c F * ((P F (d + 1) oneExp) *
              (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
                S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1)))) := by
            rw [Finset.mul_sum]
      _ = ∑ e : D.ι, ca * (D1c F * ((P F (d + 1) oneExp) *
              (((D.f e : ℤ) : RatFunc.CompletionAtInfty F) *
                S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1)))) := by
            rw [Finset.mul_sum]
      _ = ∑ e : D.ι, (ca * (D1c F * (((D.f e : ℤ) : RatFunc.CompletionAtInfty F)))) *
              (P F (d + 1) oneExp * S_lt F (D.dep e) (D.hdep e) (D.c e) (d + 1)) := by
            apply Finset.sum_congr rfl
            intro e he
            ring
      _ = ∑ e : D.ι, (ca * (D1c F * (((D.f e : ℤ) : RatFunc.CompletionAtInfty F)))) *
              S F (D.dep e + 1) (by omega : 0 < D.dep e + 1) (consVec oneExp (D.c e)) (d + 1) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [S_prepend F (d + 1) oneExp (D.hdep e) (D.c e)]
  calc
    ((a : RatFunc F) : RatFunc.CompletionAtInfty F) * (D1c F * ((P F (d + 1) oneExp) *
        (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) * S_lt F r hr t (d + 1))))
        = ca * (D1c F * ((P F (d + 1) oneExp) *
            (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) * S_lt F r hr t (d + 1)))) := by
          dsimp [ca]
    _ = ∑ e : D.ι, (ca * (D1c F * (((D.f e : ℤ) : RatFunc.CompletionAtInfty F)))) *
            S F (D.dep e + 1) (by omega : 0 < D.dep e + 1) (consVec oneExp (D.c e)) (d + 1) := by
          rw [h1, h2]
    _ = ∑ e : (p2WpT F (qMinusExp F) hr t).ι,
        (((a : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (D1c F * (((p2WpT F (qMinusExp F) hr t).f e : ℤ) : RatFunc.CompletionAtInfty F))) *
          S F ((p2WpT F (qMinusExp F) hr t).dep e + 1)
            (by omega : 0 < (p2WpT F (qMinusExp F) hr t).dep e + 1)
            (consVec oneExp ((p2WpT F (qMinusExp F) hr t).c e)) (d + 1) := by
          dsimp [D, ca]


/-- ★ BC_q in pure-output form (Prop 2.10 + (2.6)-expansion): the surviving
`D1·S_{d+1}(1)·(S_<d+1(q−1)·S_<d+1(t_j))` terms become `S_{d+1}(1 :: c_e)`-outputs,
`t_{j,e} ≤ (q−1) + t_j` (from the p2WpT data). -/
theorem BC_q_pure {ι : Type} [Fintype ι] (depA : ι → ℕ) (hdepA : ∀ i, 0 < depA i)
    (cA : ∀ i, Fin (depA i) → ℕ+) (aA : ι → RatFunc F)
    {κ : Type} [Fintype κ] (depB : κ → ℕ) (hdepB : ∀ j, 0 < depB j)
    (hB2 : ∀ j, 1 < depB j) (cB : ∀ j, Fin (depB j) → ℕ+) (aB : κ → RatFunc F)
    (hR : ∀ e : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i) (hdepA i) (cA i) e)) +
      (∑ k : κ, (((aB k : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depB k) (hdepB k) (cB k) (e + 1))) = 0) :
    ∀ d : ℕ,
      (∑ i : ι, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          S F (depA i + 1) (by omega : 0 < depA i + 1) (consVec (qExp F) (cA i)) d)) -
      (∑ j : κ, ∑ e : (p2WpT F (qMinusExp F) (hdepB j) (cB j)).ι,
          (((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
            (D1c F * (((p2WpT F (qMinusExp F) (hdepB j) (cB j)).f e : ℤ) : RatFunc.CompletionAtInfty F))) *
            S F ((p2WpT F (qMinusExp F) (hdepB j) (cB j)).dep e + 1)
              (by omega : 0 < (p2WpT F (qMinusExp F) (hdepB j) (cB j)).dep e + 1)
              (consVec oneExp ((p2WpT F (qMinusExp F) (hdepB j) (cB j)).c e)) (d + 1)) = 0 := by
  classical
  intro d
  have hB := BC_q F depA hdepA cA aA depB hdepB hB2 cB aB hR d
  have hsum : (∑ j : κ, (((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          (D1c F * ((P F (d + 1) oneExp) *
              (S_lt F 1 (by omega : 0 < 1) (single (qMinusExp F)) (d + 1) *
                S_lt F (depB j) (hdepB j) (cB j) (d + 1)))))) =
      (∑ j : κ, ∑ e : (p2WpT F (qMinusExp F) (hdepB j) (cB j)).ι,
          (((aB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
            (D1c F * (((p2WpT F (qMinusExp F) (hdepB j) (cB j)).f e : ℤ) : RatFunc.CompletionAtInfty F))) *
            S F ((p2WpT F (qMinusExp F) (hdepB j) (cB j)).dep e + 1)
              (by omega : 0 < (p2WpT F (qMinusExp F) (hdepB j) (cB j)).dep e + 1)
              (consVec oneExp ((p2WpT F (qMinusExp F) (hdepB j) (cB j)).c e)) (d + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact bterm_expand F (hdepB j) (cB j) (aB j) d
  rw [hsum] at hB
  exact hB



end ZagierHoffmanPositiveChar
