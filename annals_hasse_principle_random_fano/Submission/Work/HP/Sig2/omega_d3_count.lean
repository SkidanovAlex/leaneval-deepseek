import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.pair_counts
import Submission.Work.HP.Sig2.omega_li

/-!
# Counting pairs of small `𝔡₃`

The set of pairs `(x,y) ∈ Omega d n B` with `𝔡₃(x,y) ≤ Δ` has cardinality at most
`K · (B^{1/(n+1-d)})^6 · Δ^{n-1} · (log (2Δ))^2`, which is the specialised form of the pair
count `ℓ_{3,n}(X,Y;Δ) ≪ X³Y³Δ^{n-1}(log Δ)²` of `pair_counts` at `X = Y = B^{1/(n+1-d)}`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Sig2

open Work.HP

theorem omega_d3_count (d n : ℕ) (hn : 3 ≤ n) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ B Δ : ℝ, 1 ≤ B → 1 ≤ Δ →
      (({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ}.ncard : ℝ))
        ≤ K * (B ^ (1 / ((n : ℝ) + 1 - d))) ^ 6 * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2 := by
  obtain ⟨K, hKpos, hK⟩ := pair_counts n (by omega) 3 (by norm_num) (by omega)
  refine ⟨K, hKpos, ?_⟩
  intro B Δ hB hΔ
  set W : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hW
  have hexp : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1 - d) := by
    apply div_nonneg (by norm_num)
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hW1 : 1 ≤ W := Real.one_le_rpow hB hexp
  set T : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ W ∧ eNorm p.2 ≤ W ∧
      dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ} with hT
  have hTfin : T.Finite := by
    refine Set.Finite.subset ((finite_eNorm_le W).prod (finite_eNorm_le W)) ?_
    intro p hp
    exact ⟨hp.2.1, hp.2.2.1⟩
  have hsub : {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
        dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ} ⊆ T := by
    rintro p ⟨hOm, hd3⟩
    have h1 := hOm.1.2
    have h2 := hOm.2.1.2
    exact ⟨li_of_mem_Omega d n B p hOm, h1, h2, hd3⟩
  have hncard := Set.ncard_le_ncard hsub hTfin
  have hell : (T.ncard : ℝ) = (ellXY n 3 W W Δ : ℝ) := by
    rw [hT, ellXY] <;> rfl
  have hbound := hK W W Δ hW1 hW1 hΔ
  have hmin : 2 * min (3 - 2) 1 = 2 := by decide
  rw [hmin] at hbound
  calc (({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | p ∈ Omega d n B ∧
          dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ Δ}.ncard : ℝ))
      ≤ (T.ncard : ℝ) := by exact_mod_cast hncard
    _ = (ellXY n 3 W W Δ : ℝ) := hell
    _ ≤ K * W ^ 3 * W ^ 3 * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2 := hbound
    _ = K * W ^ 6 * Δ ^ (n - 1) * Real.log (2 * Δ) ^ 2 := by ring

end Work.HP.Sig2
