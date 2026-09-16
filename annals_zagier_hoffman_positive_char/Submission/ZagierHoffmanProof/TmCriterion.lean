import Submission.ZagierHoffmanProof.TmPhi
import Submission.ZagierHoffmanProof.GenPeriodDatum
import Submission.ZagierHoffmanProof.GenSuperLSeries
import Submission.Commons.LinearAlgebra.Matrix.det_eq_prod_diag_of_rank
import Submission.Commons.LinearAlgebra.LinearIndependent.sum_algebraMap_pow_mul_pow_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-! ## §1. The first column, `ρ` and `ϑ` of the criterion -/

section Data

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The first column `ψ` of the rigid analytic trivialisation of the merged `t`-motive, i.e. its
entries at the index of the empty tuple: `ψ_t = 𝓛(t)·ω^{w-w(t)}` and `ψ_∅ = f_∅`. -/
noncomputable def tmPsiCol (ω : PowerSeries (Ambient F)) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) :
    Option ↥(tmI S) → PowerSeries (Ambient F) :=
  fun i => tmPsiOpt (Nat.card F) ω w S cf i (⟨[], h0⟩ : ↥(tmI S))

@[simp] lemma tmPsiCol_none (ω : PowerSeries (Ambient F)) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) :
    tmPsiCol F ω w S cf h0 none = tmF (Nat.card F) ω w S cf [] := rfl

@[simp] lemma tmPsiCol_some (ω : PowerSeries (Ambient F)) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) (t : ↥(tmI S)) :
    tmPsiCol F ω w S cf h0 (some t)
      = tmL (Nat.card F) ω t.1 * ω ^ (w - tmWeight t.1) := by
  rw [tmPsiCol, tmPsiOpt_some_some]
  exact tmPsi_prefix (Nat.card F) ω w (t := t.1) (t' := ([] : List (ℕ × Polynomial (Ambient F))))
    (by simp)

/-- The row vector `ρ = (0,…,0,1)` of the criterion: it is supported on the `f_∅`-component. -/
noncomputable def tmRho (S : Finset (List (ℕ × Polynomial (Ambient F)))) :
    Option ↥(tmI S) → Ambient F :=
  fun i => if i = none then 1 else 0

/-- The `|I|` columns of the identity matrix, as a matrix indexed by `Option I × I`. -/
noncomputable def tmTheta (S : Finset (List (ℕ × Polynomial (Ambient F)))) :
    Matrix (Option ↥(tmI S)) ↥(tmI S) (Ambient F) :=
  fun i j => if i = some j then 1 else 0

@[simp] lemma tmRho_none (S : Finset (List (ℕ × Polynomial (Ambient F)))) :
    tmRho F S none = 1 := rfl

lemma tmRho_some (S : Finset (List (ℕ × Polynomial (Ambient F)))) (t : ↥(tmI S)) :
    tmRho F S (some t) = 0 := by
  simp [tmRho]

@[simp] lemma tmTheta_same (S : Finset (List (ℕ × Polynomial (Ambient F)))) (t : ↥(tmI S)) :
    tmTheta F S (some t) t = 1 := by
  simp [tmTheta]

lemma tmTheta_none (S : Finset (List (ℕ × Polynomial (Ambient F)))) (t : ↥(tmI S)) :
    tmTheta F S none t = 0 := by
  simp [tmTheta]

lemma tmTheta_ne (S : Finset (List (ℕ × Polynomial (Ambient F)))) {i : Option ↥(tmI S)}
    {j : ↥(tmI S)} (h : i ≠ some j) : tmTheta F S i j = 0 := by
  simp [tmTheta, h]

lemma tmRho_ne_zero (S : Finset (List (ℕ × Polynomial (Ambient F)))) :
    tmRho F S ≠ 0 := by
  intro h
  have := congrFun h none
  simp [tmRho] at this

lemma vecMul_tmRho_tmTheta (S : Finset (List (ℕ × Polynomial (Ambient F)))) :
    vecMul (tmRho F S) (tmTheta F S) = 0 := by
  funext j
  rw [Matrix.vecMul, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  cases i with
  | none => rw [tmRho_none, tmTheta_none, one_mul]
  | some t =>
    by_cases h : t = j
    · subst h; rw [tmRho_some, zero_mul]
    · rw [tmTheta_ne F S (by simpa using h), mul_zero]

lemma linearIndependent_tmTheta (S : Finset (List (ℕ × Polynomial (Ambient F)))) :
    LinearIndependent (Ambient F) (fun j : ↥(tmI S) => fun i : Option ↥(tmI S) =>
      tmTheta F S i j) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h : (∑ c : ↥(tmI S),
      g c * (if (some j : Option ↥(tmI S)) = some c then (1 : Ambient F) else 0)) = 0 := by
    have h1 := congrFun hg (some j)
    simpa [Finset.sum_apply, tmTheta] using h1
  rw [Finset.sum_eq_single j] at h
  · simpa using h
  · intro c _ hc
    have hcj : ¬ ((some j : Option ↥(tmI S)) = some c) := by
      rintro hh; exact hc (Option.some.inj hh).symm
    simp [hcj]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma mem_tmI_entry {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {t : List (ℕ × Polynomial (Ambient F))} (ht : t ∈ tmI S)
    {y : ℕ × Polynomial (Ambient F)} (hy : y ∈ t) : ∃ s ∈ S, y ∈ s := by
  obtain ⟨s, hs, k, hk, rfl⟩ := mem_tmI.mp ht
  exact ⟨s, hs, List.mem_of_mem_take hy⟩

lemma tmF_nil {w : ℕ} (ω : PowerSeries (Ambient F))
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)) :
    tmF (Nat.card F) ω w S cf [] = ∑ s ∈ S, (cf s : PowerSeries (Ambient F)) * tmL (Nat.card F) ω s := by
  rw [tmF]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

/-- **Chang's Lemma 5.3.1 for the first column**: every entry of `ψ` is super-entire. -/
theorem tmPsiCol_superEntire {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F) {w : ℕ} {ω : PowerSeries (Ambient F)}
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hS : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) :
    ∀ i, GSuperEntire γ (tmPsiCol F ω w S cf h0 i) := by
  intro i
  cases i with
  | some t =>
    rw [tmPsiCol_some]
    have hL : ∀ x ∈ (tmCoe (K := Ambient F) t.1).reverse,
        GIsSmall γ (ω ^ x.1 * x.2) := by
      intro x hx
      rw [List.mem_reverse, tmCoe, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨s, hs, hy'⟩ := mem_tmI_entry F t.2 hy
      exact hS s hs y hy'
    have hLse : ∀ x ∈ (tmCoe (K := Ambient F) t.1).reverse,
        GSuperEntire γ x.2 := by
      intro x hx
      rw [List.mem_reverse, tmCoe, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨s, hs, hy'⟩ := mem_tmI_entry F t.2 hy
      exact hSse s hs y hy'
    exact gSuperEntire_atLrGen_mul_pow hγ1 harch hq hω hωse hL hLse (w - tmWeight t.1)
  | none =>
    rw [tmPsiCol_none, tmF_nil]
    refine GSuperEntire.sum hγ1.le S
      (fun s => (cf s : PowerSeries (Ambient F)) * tmL (Nat.card F) ω s) fun s hs => ?_
    refine (GSuperEntire.polynomial hγ0 hγ1.le (cf s)).mul hγ1.le ?_
    have h1 : ∀ x ∈ tmCoe (K := Ambient F) s, GIsSmall γ (ω ^ x.1 * x.2) := by
      intro x hx
      rw [tmCoe, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hS s hs y hy
    have h2 : ∀ x ∈ tmCoe (K := Ambient F) s, GSuperEntire γ x.2 := by
      intro x hx
      rw [tmCoe, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hSse s hs y hy
    exact gSuperEntire_atLrPaperGen hγ1 harch hq hω hωse h1 h2

/-- **The criterion's `hfe`**: the first column `ψ` of the trivialisation satisfies
`ψ = Φ^{(1)}·ψ^{(1)}`, where `Φ` is the coefficientwise `q`-th root of the merged `t`-motive. -/
theorem tmPsiCol_functional {w : ℕ} {ω : PowerSeries (Ambient F)} {γ : ℚᵐ⁰}
    (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S,
      frobTwist (R := Ambient F) (p := Nat.card F) 1 ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0) :
    tmPsiCol F ω w S cf h0
      = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix
            (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA))).mulVec
        (frobTwistVec (q := Nat.card F) 1 (tmPsiCol F ω w S cf h0)) := by
  funext i
  rw [tmPhi_twist_mat]
  have h := congrFun (congrFun (tmPsiOpt_functional (S := S) (cf := cf) (q := Nat.card F)
    (θ := ambTheta F) (ω := ω) (w := w) hγ harch hq hω hωfe hw hcf hsm hne) i)
    (⟨[], h0⟩ : ↥(tmI S))
  rw [Matrix.mul_apply] at h
  simpa [tmPsiCol, tmPsiOpt, frobTwistVec_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    frobTwistMat_apply, Matrix.mulVec, dotProduct] using h

end Data

end ZagierHoffmanPositiveChar
