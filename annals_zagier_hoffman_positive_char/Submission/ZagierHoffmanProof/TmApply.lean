import Submission.ZagierHoffmanProof.TmCriterion
import Submission.ZagierHoffmanProof.ABPAssemble

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial Matrix Finset
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

/-!
# Applying the ABP criterion to the merged dual `t`-motive

The Anderson–Brownawell–Papanikolas criterion (`ABPAssemble.ABP_criterion`) is stated for
matrices indexed by `Fin ℓ`, `ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1))`.  The `t`-motive of Dac §4.2 is
indexed by `Option ↥(tmI S)` (the empty tuple plus the nonempty tuples in `S`), whose matrix
`ϑ` (`tmTheta`) has `Fintype.card ↥(tmI S) = ℓ - 1` columns.

This file contains the reindexing: the criterion in the form needed (`ABP_criterion_of_fintype`,
for an arbitrary finite index type), and then its application to the `t`-motive (`tmABP`).
-/

variable (F : Type*) [Field F] [Finite F]

/-! ## §1. Reindexing lemmas -/

section Reindex

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Precomposing every member of a linearly independent family of functions with an equivalence
preserves linear independence. -/
lemma linearIndependent_precomp_equiv {ι ι' ι'' : Type*} {v : ι → ι' → M}
    (hv : LinearIndependent R v) (e : ι'' ≃ ι') :
    LinearIndependent R (fun t => v t ∘ e) := by
  rw [linearIndependent_iff'ₛ] at hv ⊢
  intro s f g hfg i hi
  refine hv s f g ?_ i hi
  ext x
  simpa [Function.comp_def, Pi.smul_apply, Finset.sum_apply] using congrFun hfg (e.symm x)

variable {α : Type*} [NonUnitalNonAssocSemiring α]

/-- Reindexing a matrix–vector product along an equivalence. -/
lemma submatrix_mulVec_comp_equiv {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m α) (v : m → α) (e : n ≃ m) :
    (A.submatrix (⇑e) (⇑e)) *ᵥ (v ∘ ⇑e) = (A *ᵥ v) ∘ ⇑e := by
  have h : ((v ∘ ⇑e) ∘ ⇑e.symm) = v := by
    funext x
    simp [Function.comp_apply]
  have h2 := submatrix_mulVec_equiv (M := A) (v := v ∘ ⇑e) (e₁ := (⇑e : n → m)) (e₂ := e)
  simp only [h2, h]

end Reindex

/-! ## §2. The ABP criterion for an arbitrary finite index type -/

/-- The Anderson–Brownawell–Papanikolas criterion with the index set an arbitrary finite type
instead of `Fin ℓ`: this is the form in which it is applied to the dual `t`-motive. -/
theorem ABP_criterion_of_fintype {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] (ν : ℕ)
    (hℓ : 2 ≤ Fintype.card ι) (hJ : Fintype.card J = Fintype.card ι - 1)
    {Φ : Matrix ι ι (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν)
    {ϑ : Matrix ι J (Ambient F)} (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1)
    {ψ : ι → PowerSeries (Ambient F)} (hse : ∀ i, GSuperEntire γ (ψ i))
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    (hind : LinearIndependent (Ambient F) (fun j : J => fun i : ι => ϑ i j))
    {ρ : ι → Ambient F} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0)
    (hval : dotProduct ρ (fun i => evalSeriesGen (ψ i) (ambTheta F)) = 0)
    {c : Ambient F} (hc : c ≠ 0) {s : ℕ}
    (hdet : Φ.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s) :
    ∃ P : ι → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * ψ j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = ρ j) := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with hedef
  set eJ : J ≃ Fin (Fintype.card ι - 1) := Fintype.equivFinOfCardEq hJ with heJdef
  let Φ' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) (Polynomial (Ambient F)) :=
    Φ.submatrix (⇑e.symm) (⇑e.symm)
  let ψ' : Fin (Fintype.card ι) → PowerSeries (Ambient F) := fun i => ψ (e.symm i)
  let ρ' : Fin (Fintype.card ι) → Ambient F := fun i => ρ (e.symm i)
  let ϑ' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι - 1)) (Ambient F) :=
    fun i j => ϑ (e.symm i) (eJ.symm j)
  have hΦ' : ∀ i j m, (Φ' i j).coeff m ∈ ambA F ν := fun i j m => hΦ _ _ _
  have hϑ' : ∀ i j, ϑ' i j ∈ ambA F ν := fun i j => hϑ _ _
  have hse' : ∀ i, GSuperEntire γ (ψ' i) := fun i => hse (e.symm i)
  have hfe' : ψ' = (frobTwistMat (q := Nat.card F) 1
      ((coeHom (K := Ambient F)).mapMatrix Φ')).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ') := by
    have hN : frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ')
        = (frobTwistMat (q := Nat.card F) 1
            ((coeHom (K := Ambient F)).mapMatrix Φ)).submatrix (⇑e.symm) (⇑e.symm) := by
      ext i j
      simp [Φ', frobTwistMat, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.submatrix_apply]
    have hv : frobTwistVec (q := Nat.card F) 1 ψ'
        = (frobTwistVec (q := Nat.card F) 1 ψ) ∘ (⇑e.symm) := by
      funext i; simp [ψ', frobTwistVec_apply]
    have hvec := submatrix_mulVec_comp_equiv
      (A := frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ))
      (v := frobTwistVec (q := Nat.card F) 1 ψ) (e := e.symm)
    rw [hN, hv, hvec, ← hfe]
    rfl
  have hind' : LinearIndependent (Ambient F)
      (fun j : Fin (Fintype.card ι - 1) => fun i : Fin (Fintype.card ι) => ϑ' i j) := by
    have hv : LinearIndependent (Ambient F)
        (fun t : J => fun i : Fin (Fintype.card ι) => ϑ (e.symm i) t) :=
      linearIndependent_precomp_equiv (v := fun j : J => fun i : ι => ϑ i j) hind e.symm
    have h2 := hv.comp (⇑eJ.symm) eJ.symm.injective
    simpa [ϑ', Function.comp_def] using h2
  have hρ' : Matrix.vecMul ρ' ϑ' = 0 := by
    have h1 : ϑ' = ϑ.submatrix (⇑e.symm) (⇑eJ.symm) := rfl
    have h2 : (ρ' ∘ (⇑e : ι → Fin (Fintype.card ι))) = ρ := by funext k; simp [ρ']
    have h3 := submatrix_vecMul_equiv (M := ϑ) (v := ρ') (e₁ := e.symm)
      (e₂ := (⇑eJ.symm : Fin (Fintype.card ι - 1) → J))
    rw [h1, h3, Equiv.symm_symm, h2, hρ]
    funext j
    rfl
  have hρ0' : ρ' ≠ 0 := by
    intro h
    refine hρ0 (funext fun i => ?_)
    have := congrFun h (e i)
    simpa [ρ'] using this
  have hval' : dotProduct ρ' (fun i => evalSeriesGen (ψ' i) (ambTheta F)) = 0 := by
    have h1 : ρ' = ρ ∘ (⇑e.symm) := by funext i; simp [ρ']
    have h2 : (fun i => evalSeriesGen (ψ' i) (ambTheta F))
        = (fun i : ι => evalSeriesGen (ψ i) (ambTheta F)) ∘ (⇑e.symm) := by
      funext i; simp [ψ']
    have hEq : dotProduct ρ' (fun i => evalSeriesGen (ψ' i) (ambTheta F))
        = dotProduct ρ (fun i : ι => evalSeriesGen (ψ i) (ambTheta F)) := by
      rw [h1, h2]
      exact comp_equiv_dotProduct_comp_equiv (x := ρ)
        (y := fun i : ι => evalSeriesGen (ψ i) (ambTheta F)) e.symm
    rw [hEq, hval]
  have hdet' : Φ'.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s := by
    have h1 : Φ' = Φ.submatrix (⇑e.symm) (⇑e.symm) := rfl
    rw [h1, Matrix.det_submatrix_equiv_self e.symm Φ, hdet]
  obtain ⟨P', hP'1, hP'2⟩ :=
    ABP_criterion F ν hℓ hΦ' hϑ' hγ0 hγ hse' hfe' hind' hρ' hρ0' hval' hc hdet'
  refine ⟨fun i => P' (e i), ?_, ?_⟩
  · have hsum : (∑ j : ι, coeHom (K := Ambient F) (P' (e j)) * ψ j)
        = ∑ k : Fin (Fintype.card ι), coeHom (K := Ambient F) (P' k) * ψ' k :=
      Fintype.sum_equiv e _ _ (fun j => by simp [ψ'])
    rw [hsum, hP'1]
  · intro j
    have := hP'2 (e j)
    simpa [ρ'] using this

/-! ## §3. The criterion for the merged dual `t`-motive -/

/-- **The ABP criterion applied to the merged dual `t`-motive** (Dac §5.1).  Given the datum
`(ω, w, S, cf)` with all tuples of `S` of weight `w`, `A_0`-coefficients, and the input
`hval : f_∅(θ) = 0`, there is a polynomial row vector `P` with `P·ψ = 0` and `P(θ) = ρ`. -/
theorem tmABP {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F)
    {w : ℕ} {ω : PowerSeries (Ambient F)} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    (hval : dotProduct (tmRho F S)
      (fun i => evalSeriesGen (tmPsiCol F ω w S cf h0 i) (ambTheta F)) = 0) :
    ∃ P : Option ↥(tmI S) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * tmPsiCol F ω w S cf h0 j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F S j) := by
  classical
  have hℓ : 2 ≤ Fintype.card (Option ↥(tmI S)) := by
    rw [Fintype.card_option]
    exact Nat.succ_le_succ (Fintype.card_pos_iff.mpr ⟨⟨[], h0⟩⟩)
  have hJ : Fintype.card ↥(tmI S) = Fintype.card (Option ↥(tmI S)) - 1 := by
    rw [Fintype.card_option]
    omega
  have hϑ : ∀ i j, tmTheta F S i j ∈ ambA F 1 := by
    intro i j
    by_cases h : i = some j
    · simp only [tmTheta, if_pos h]; exact ambA_one_mem F 1
    · simp only [tmTheta, if_neg h]; exact (ambASub F 1).zero_mem
  have hdet : (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA).det
      = Polynomial.C (1 : Ambient F) * (Polynomial.X - Polynomial.C (ambTheta F)) ^
        (∑ t : ↥(tmI S), (w - tmWeight t.1)) := by
    rw [det_tmPhi F w S cf hA]
    simp
  exact ABP_criterion_of_fintype (F := F) 1 hℓ hJ
    (tmPhi_coeff_mem F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA)
    hϑ hγ0 hγ
    (tmPsiCol_superEntire F hγ0 hγ harch hq hω hωse hsm hSse h0)
    (tmPsiCol_functional F hγ harch hq hω hωfe hw hcf hsm hne h0 hA)
    (linearIndependent_tmTheta F S)
    (vecMul_tmRho_tmTheta F S) (tmRho_ne_zero F S) hval one_ne_zero hdet

/-! ## §4. The augmented first column: Dac's `Φ̃ = diag(1, Φ)` and `ρ = (a,0,…,0,1)`

Dac's linear relation (LD) is `a + ∑_i a_i·𝓛(s_i;Q_i)(θ) = 0` with `a ∈ A`; the `f_∅`-entry of
the first column is `f_∅ = ∑_i a_i(t)·𝓛(s_i;Q_i)`, so `f_∅(θ) = -a` need NOT vanish.  In the paper
this is handled by passing to `Φ̃ = diag(1,Φ)` and `ρ = (a,0,…,0,1)`.

In the merged `t`-motive the `none`-column of `A` is `e_none` (`A (some t) none = 0`,
`A none none = 1`), so the `none`-coordinate of the first column satisfies `ψ_none = ψ_none^{(1)}`.
Hence adding the twist-invariant constant `a` to `ψ_none` preserves the functional equation, and
the extra coordinate of the paper's `Φ̃` can simply be merged into the `f`-row.  The resulting
column is `tmPsiColA`, and the criterion's `ρψ(θ) = 0` becomes `f_∅(θ) + a = 0`. -/

section Augmented

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The augmented first column `ψ_a = ψ + a·e_none`. -/
noncomputable def tmPsiColA (ω : PowerSeries (Ambient F)) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (a : Polynomial (Ambient F)) : Option ↥(tmI S) → PowerSeries (Ambient F) :=
  fun i => tmPsiCol F ω w S cf h0 i
    + (if i = none then ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)) else 0)

@[simp] lemma tmPsiColA_none (ω : PowerSeries (Ambient F)) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) (a : Polynomial (Ambient F)) :
    tmPsiColA F ω w S cf h0 a none
      = tmF (Nat.card F) ω w S cf [] + ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  simp [tmPsiColA]

@[simp] lemma tmPsiColA_some (ω : PowerSeries (Ambient F)) (w : ℕ)
    (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) (a : Polynomial (Ambient F))
    (t : ↥(tmI S)) :
    tmPsiColA F ω w S cf h0 a (some t)
      = tmL (Nat.card F) ω t.1 * ω ^ (w - tmWeight t.1) := by
  simp [tmPsiColA]

/-- The `none`-coordinate of `tmRho`-weighted sums. -/
@[simp] lemma dotProduct_tmRho (v : Option ↥(tmI S) → Ambient F) :
    dotProduct (tmRho F S) v = v none := by
  classical
  rw [dotProduct, Finset.sum_eq_single none]
  · simp
  · intro j _ hj; simp [tmRho, hj]
  · intro h; exact absurd (Finset.mem_univ none) h

/-- **Chang's Lemma 5.3.1 for the augmented column**. -/
theorem tmPsiColA_superEntire {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F) {w : ℕ} {ω : PowerSeries (Ambient F)}
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hS : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S) (a : Polynomial (Ambient F)) :
    ∀ i, GSuperEntire γ (tmPsiColA F ω w S cf h0 a i) := by
  intro i
  cases i with
  | none =>
    rw [tmPsiColA_none]
    exact (tmPsiCol_superEntire F (w := w) (ω := ω) (cf := cf) hγ0 hγ1 harch hq hω hωse hS hSse h0 none).add
      (GSuperEntire.polynomial hγ0 hγ1.le a)
  | some t =>
    rw [tmPsiColA_some]
    exact tmPsiCol_superEntire F (w := w) (ω := ω) (cf := cf) hγ0 hγ1 harch hq hω hωse hS hSse h0 (some t)

/-- **The functional equation for the augmented column**: `ψ_a` satisfies the same
`ψ = Φ^{(1)}ψ^{(1)}` as `ψ`, because the `none`-column of `A` is `e_none`. -/
theorem tmPsiColA_functional {w : ℕ} {ω : PowerSeries (Ambient F)} {γ : ℚᵐ⁰}
    (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))) :
    tmPsiColA F ω w S cf h0 a
      = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix
            (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA))).mulVec
        (frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a)) := by
  classical
  let e : Option ↥(tmI S) → PowerSeries (Ambient F) :=
    fun j => if j = none then ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)) else 0
  have hsplit : tmPsiColA F ω w S cf h0 a = tmPsiCol F ω w S cf h0 + e := rfl
  have htw : frobTwistVec (q := Nat.card F) 1 (tmPsiCol F ω w S cf h0 + e)
      = frobTwistVec (q := Nat.card F) 1 (tmPsiCol F ω w S cf h0) + e := by
    funext j
    simp only [frobTwistVec_apply, Pi.add_apply, frobTwist_add]
    congr 1
    rcases j with _ | t
    · simp [e, ha]
    · simp [e]
  have hbase := tmPsiCol_functional F (w := w) (ω := ω) hγ harch hq hω hωfe hw hcf hsm hne h0
    hA
  have hN := tmPhi_twist_mat F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA
  have hev : ((coeHom (K := Ambient F)).mapMatrix
        (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf)).mulVec e = e := by
    funext i
    rw [Matrix.mulVec_apply_eq_sum,
      Finset.sum_eq_single none (fun j _ hj => by simp [e, hj])
        (fun h => absurd (Finset.mem_univ none) h)]
    rcases i with _ | t
    · simp [e, RingHom.mapMatrix_apply, Matrix.map_apply, coeHom_apply, tmAOpt_none_none]
    · simp [e, RingHom.mapMatrix_apply, Matrix.map_apply, coeHom_apply, tmAOpt_some_none]
  rw [hsplit, htw, Matrix.mulVec_add]
  funext i
  simp only [Pi.add_apply, congrFun hbase i, congrFun hev i, hN]

/-- **The ABP criterion for the merged dual `t`-motive, with Dac's constant term `a`** (Dac §5.1):
given `f_∅(θ) + a(θ) = 0` there is a polynomial row vector `P` with `P·ψ_a = 0` and
`P(θ) = ρ`. -/
theorem tmABP_a {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F)
    {w : ℕ} {ω : PowerSeries (Ambient F)} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) ω w S cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0) :
    ∃ P : Option ↥(tmI S) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * tmPsiColA F ω w S cf h0 a j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F S j) := by
  classical
  have hℓ : 2 ≤ Fintype.card (Option ↥(tmI S)) := by
    rw [Fintype.card_option]
    exact Nat.succ_le_succ (Fintype.card_pos_iff.mpr ⟨⟨[], h0⟩⟩)
  have hJ : Fintype.card ↥(tmI S) = Fintype.card (Option ↥(tmI S)) - 1 := by
    rw [Fintype.card_option]
    omega
  have hϑ : ∀ i j, tmTheta F S i j ∈ ambA F 1 := by
    intro i j
    by_cases h : i = some j
    · simp only [tmTheta, if_pos h]; exact ambA_one_mem F 1
    · simp only [tmTheta, if_neg h]; exact (ambASub F 1).zero_mem
  have hdet : (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA).det
      = Polynomial.C (1 : Ambient F) * (Polynomial.X - Polynomial.C (ambTheta F)) ^
        (∑ t : ↥(tmI S), (w - tmWeight t.1)) := by
    rw [det_tmPhi F w S cf hA]
    simp
  have hse' := tmPsiColA_superEntire F (w := w) (cf := cf) hγ0 hγ harch hq hω hωse hsm hSse h0 a
  have hFse : GSuperEntire γ (tmF (Nat.card F) ω w S cf
      ([] : List (ℕ × Polynomial (Ambient F)))) := by
    have h := tmPsiCol_superEntire F (w := w) (ω := ω) (cf := cf) hγ0 hγ harch hq hω hωse hsm
      hSse h0 (none : Option ↥(tmI S))
    simpa using h
  have hAa : GSuperEntire γ (((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))) :=
    GSuperEntire.polynomial hγ0 hγ.le a
  have hval' : dotProduct (tmRho F S)
      (fun i => evalSeriesGen (tmPsiColA F ω w S cf h0 a i) (ambTheta F)) = 0 := by
    rw [dotProduct_tmRho, tmPsiColA_none,
      evalSeriesGen_add hγ harch hFse hAa (ambTheta F), evalSeriesGen_polynomial]
    exact hval
  exact ABP_criterion_of_fintype (F := F) 1 hℓ hJ
    (tmPhi_coeff_mem F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA)
    hϑ hγ0 hγ hse'
    (tmPsiColA_functional F hγ harch hq hω hωfe hw hcf hsm hne h0 hA ha)
    (linearIndependent_tmTheta F S)
    (vecMul_tmRho_tmTheta F S) (tmRho_ne_zero F S) hval' one_ne_zero hdet

end Augmented

/-! ## §5. Step 2 of Dac §5.2: the polynomial annihilator `B̃`

Given the polynomial row vector `P` with `P·ψ_a = 0` and `P(θ) = ρ` (so that `Q := P_none` has
`Q(θ) = 1 ≠ 0`), the *second* relation of Dac's Step 2 is

  `(g^{(1)} - gA)·ψ_a^{(1)} = 0`,  where `g = P/Q`, and `g^{(1)} - gA` has last coordinate `0`
  because the `none`-column of `A` is `e_none`.

Clearing the denominator `Q` turns this into the POLYNOMIAL row vector

  `B̃ := Q·P^{(1)} - Q^{(1)}·(P·A)`,   `B̃_none = 0`,   `∑_j B̃_j·(ψ_a^{(1)})_j = 0`.

Working with `B̃` instead of `g` avoids introducing the field of rational functions `K̄(t)`. -/

section Step2

variable {w : ℕ} {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- The polynomial row vector `B̃ = Q·P^{(1)} - Q^{(1)}·(P·A)` of Dac §5.2. -/
noncomputable def tmB (w : ℕ) (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (P : Option ↥(tmI S) → Polynomial (Ambient F)) :
    Option ↥(tmI S) → Polynomial (Ambient F) :=
  fun j => P none * polyTwist (q := Nat.card F) 1 (P j)
    - polyTwist (q := Nat.card F) 1 (P none)
        * ∑ i, P i * tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j

/-- The `none`-column of `A` is `e_none`: `∑_i P_i·A_{i,none} = P_none`. -/
lemma sum_mul_tmAOpt_none (w : ℕ) (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (P : Option ↥(tmI S) → Polynomial (Ambient F)) :
    (∑ i, P i * tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i none) = P none := by
  rw [Finset.sum_eq_single none]
  · simp
  · intro i _ hi
    rcases i with _ | t
    · exact absurd rfl hi
    · simp
  · intro h; exact absurd (Finset.mem_univ none) h

/-- The `none`-entry of `B̃` vanishes (this is the point of the `Q`-weighting). -/
lemma tmB_none (w : ℕ) (S : Finset (List (ℕ × Polynomial (Ambient F))))
    (cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F))
    (P : Option ↥(tmI S) → Polynomial (Ambient F)) :
    tmB F w S cf P none = 0 := by
  rw [tmB, sum_mul_tmAOpt_none]
  ring

/-- **The relation satisfied by `B̃`**: if `P·ψ = 0` and `ψ = A·ψ^{(1)}` then
`∑_j B̃_j·ψ^{(1)}_j = 0`. -/
theorem tmB_relation (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {ψ : Option ↥(tmI S) → PowerSeries (Ambient F)}
    (hfe : ψ = (coeHom (K := Ambient F)).mapMatrix
        (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
      frobTwistVec (q := Nat.card F) 1 ψ)
    {P : Option ↥(tmI S) → Polynomial (Ambient F)}
    (hP : ∑ j, coeHom (K := Ambient F) (P j) * ψ j = 0) :
    (∑ j, coeHom (K := Ambient F) (tmB F w S cf P j)
      * frobTwistVec (q := Nat.card F) 1 ψ j) = 0 := by
  classical
  have hψ : ∀ i, ψ i = ∑ j, (coeHom (K := Ambient F)
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j) := by
    intro i
    have h := congrFun hfe i
    simp only [Matrix.mulVec_apply_eq_sum, RingHom.mapMatrix_apply, Matrix.map_apply,
      frobTwistVec_apply] at h
    exact h
  have hPt : (∑ j, frobTwist (R := Ambient F) (p := Nat.card F) 1 (coeHom (K := Ambient F) (P j))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j)) = 0 := by
    have h := congrArg (frobTwist (R := Ambient F) (p := Nat.card F) 1) hP
    rw [frobTwist_zero, frobTwist_sum] at h
    simpa only [frobTwist_mul] using h
  have hmain : ∀ j, coeHom (K := Ambient F) (tmB F w S cf P j)
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j)
      = coeHom (K := Ambient F) (P none)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (coeHom (K := Ambient F) (P j))
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j))
        - frobTwist (R := Ambient F) (p := Nat.card F) 1 (coeHom (K := Ambient F) (P none))
          * ((∑ i, coeHom (K := Ambient F) (P i)
              * coeHom (K := Ambient F)
                (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j))
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j)) := by
    intro j
    rw [tmB]
    simp only [map_sub, map_mul, map_sum, coe_polyTwist]
    ring
  have h2 : (∑ x, (∑ i, coeHom (K := Ambient F) (P i)
      * coeHom (K := Ambient F)
        (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i x))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ x)) = 0 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    trans ∑ i, coeHom (K := Ambient F) (P i) * ψ i
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hψ i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    · exact hP
  have hsum : (∑ j, coeHom (K := Ambient F) (tmB F w S cf P j)
      * frobTwistVec (q := Nat.card F) 1 ψ j)
      = ∑ j, (coeHom (K := Ambient F) (P none)
          * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (coeHom (K := Ambient F) (P j))
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j))
        - frobTwist (R := Ambient F) (p := Nat.card F) 1 (coeHom (K := Ambient F) (P none))
          * ((∑ i, coeHom (K := Ambient F) (P i)
              * coeHom (K := Ambient F)
                (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j))
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (ψ j))) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [frobTwistVec_apply]
    exact hmain j
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hPt, h2]
  ring

end Step2

/-! ## §6. Evaluating the relation at `θ^{q^j}`: the leading-weight relation

`tmB_relation` produces a power-series identity `∑_t c_t·Ω₁^{w-w(t)} = 0` with `Ω₁ = frobTwist 1 ω`.
Factoring out `Ω₁^(w-w₀)` and cancelling (the power series ring has no zero divisors) gives
`∑_t c_t·Ω₁^(w₀-w(t)) = 0`; evaluating at `θ^{q^j}` kills every term with `tmWeight t < w₀`
(because `Ω₁(θ^{q^j}) = 0`) and leaves the **leading-weight relation**

  `∑_{t : tmWeight t = w₀} B_t(θ^{q^j})·(𝓛(t)(θ))^(q^j) = 0`,

which is the input of the MZ-property / descent argument. -/

section EvalStep

variable {w : ℕ} {ω : PowerSeries (Ambient F)} {γ : ℚᵐ⁰}
variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

theorem tmB_eval_zero (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hωse : GSuperEntire γ ω)
    (hΩ0 : (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω).coeff 0 ≠ 0)
    (hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0)
    (hMZ : ∀ (t : ↥(tmI S)) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k))
    (hLse : ∀ t : ↥(tmI S), GSuperEntire γ (tmL (Nat.card F) ω t.1))
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (hfe : tmPsiColA F ω w S cf h0 a
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a))
    {P : Option ↥(tmI S) → Polynomial (Ambient F)}
    (hP : ∑ j, coeHom (K := Ambient F) (P j) * tmPsiColA F ω w S cf h0 a j = 0)
    {w₀ : ℕ} (hw₀ : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w₀) (hw₀le : w₀ ≤ w) :
    ∀ j : ℕ, 2 ≤ j →
      (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
        (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
          * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F))
              ^ (Nat.card F ^ j)) = 0 := by
  intro j hj
  classical
  set Ω₁ := frobTwist (R := Ambient F) (p := Nat.card F) 1 ω with hΩ₁def
  have hΩ₁se : GSuperEntire γ Ω₁ := by rw [hΩ₁def]; exact hωse.frobTwist hγ.le 1
  have hΩ₁ne : Ω₁ ≠ 0 := by
    intro hz
    have h : PowerSeries.coeff 0 Ω₁ = 0 := by rw [hz, map_zero]
    exact hΩ0 h
  -- (1) the polynomial relation, split into the `none` and the `some` parts
  have hrel := tmB_relation F (w := w) (S := S) (cf := cf) hA hfe hP
  rw [Fintype.sum_option] at hrel
  have hnone : coeHom (K := Ambient F) (tmB F w S cf P none)
      * frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) none = 0 := by
    rw [tmB_none, map_zero, zero_mul]
  rw [hnone, zero_add] at hrel
  -- (2) pull out the entries of the twisted column
  have hterm : ∀ t : ↥(tmI S), coeHom (K := Ambient F) (tmB F w S cf P (some t))
      * frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) (some t)
      = coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * Ω₁ ^ (w - tmWeight t.1)) := by
    intro t
    rw [frobTwistVec_apply, tmPsiColA_some, frobTwist_mul, frobTwist_pow, hΩ₁def]
  rw [show (∑ t : ↥(tmI S), coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) (some t))
      = ∑ t : ↥(tmI S), coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * Ω₁ ^ (w - tmWeight t.1)) from Finset.sum_congr rfl (fun t _ => hterm t)] at hrel
  -- (3) factor out `Ω₁ ^ (w - w₀)` and cancel it
  have hfact : (∑ t : ↥(tmI S), coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * (frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * Ω₁ ^ (w - tmWeight t.1)))
      = Ω₁ ^ (w - w₀) * ∑ t : ↥(tmI S),
          (coeHom (K := Ambient F) (tmB F w S cf P (some t))
            * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
            * Ω₁ ^ (w₀ - tmWeight t.1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hpow : Ω₁ ^ (w - tmWeight t.1)
        = Ω₁ ^ (w - w₀) * Ω₁ ^ (w₀ - tmWeight t.1) := by
      have h1 : tmWeight t.1 ≤ w₀ := hw₀ t
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  rw [hfact] at hrel
  have hlead : (∑ t : ↥(tmI S), (coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * Ω₁ ^ (w₀ - tmWeight t.1))) = 0 :=
    (mul_eq_zero.mp hrel).resolve_left (pow_ne_zero _ hΩ₁ne)
  -- (4) evaluate at `θ ^ (q ^ j)`
  have hsuper : ∀ t ∈ (Finset.univ : Finset ↥(tmI S)),
      GSuperEntire γ (coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * Ω₁ ^ (w₀ - tmWeight t.1)) := by
    intro t _
    exact GSuperEntire.mul hγ.le (GSuperEntire.mul hγ.le
      (GSuperEntire.polynomial hγ0 hγ.le (tmB F w S cf P (some t)))
      ((hLse t).frobTwist hγ.le 1))
      (hΩ₁se.pow hγ.le _)
  have hlead2 : evalSeriesGen (∑ t ∈ (Finset.univ : Finset ↥(tmI S)),
        (coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * Ω₁ ^ (w₀ - tmWeight t.1))) ((ambTheta F) ^ (Nat.card F) ^ j) = 0 := by
    rw [hlead, evalSeriesGen_def]
    simp
  rw [evalSeriesGen_finset_sum hγ harch _ _ hsuper] at hlead2
  -- (5) compute each term
  have hcompute : ∀ t : ↥(tmI S),
      evalSeriesGen (coeHom (K := Ambient F) (tmB F w S cf P (some t))
        * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
        * Ω₁ ^ (w₀ - tmWeight t.1)) ((ambTheta F) ^ (Nat.card F) ^ j)
      = (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)
        * (evalSeriesGen Ω₁ ((ambTheta F) ^ (Nat.card F) ^ j)) ^ (w₀ - tmWeight t.1) := by
    intro t
    have htw : evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1
        (tmL (Nat.card F) ω t.1)) ((ambTheta F) ^ (Nat.card F) ^ j)
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j) := by
      have hq : (Nat.card F) ^ (j - 1) * Nat.card F = (Nat.card F) ^ j := by
        conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ j by omega)]
        rw [pow_succ]
      have hp : ((ambTheta F) ^ (Nat.card F ^ (j - 1))) ^ (Nat.card F)
          = (ambTheta F) ^ (Nat.card F) ^ j := by
        rw [← pow_mul, hq]
      have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) (hLse t)
        ((ambTheta F) ^ (Nat.card F ^ (j - 1))) 1
      rw [pow_one] at h
      rw [hp, hMZ t (j - 1), ← pow_mul, hq] at h
      exact h
    simp only [coeHom_apply]
    rw [evalSeriesGen_mul hγ harch
        (GSuperEntire.mul hγ.le
          (GSuperEntire.polynomial hγ0 hγ.le (tmB F w S cf P (some t)))
          ((hLse t).frobTwist hγ.le 1)) (hΩ₁se.pow hγ.le _) _,
      evalSeriesGen_mul hγ harch
        (GSuperEntire.polynomial hγ0 hγ.le (tmB F w S cf P (some t)))
        ((hLse t).frobTwist hγ.le 1) _,
      evalSeriesGen_polynomial, htw, evalSeriesGen_pow hγ harch hΩ₁se _ _]
  rw [show (∑ t ∈ (Finset.univ : Finset ↥(tmI S)),
        evalSeriesGen (coeHom (K := Ambient F) (tmB F w S cf P (some t))
          * frobTwist (R := Ambient F) (p := Nat.card F) 1 (tmL (Nat.card F) ω t.1)
          * Ω₁ ^ (w₀ - tmWeight t.1)) ((ambTheta F) ^ (Nat.card F) ^ j))
      = ∑ t ∈ (Finset.univ : Finset ↥(tmI S)),
        ((tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)
        * (evalSeriesGen Ω₁ ((ambTheta F) ^ (Nat.card F) ^ j)) ^ (w₀ - tmWeight t.1))
      from Finset.sum_congr rfl (fun t _ => hcompute t)] at hlead2
  -- (6) only the leading weight survives
  have hzero : ∀ t ∈ (Finset.univ : Finset ↥(tmI S)),
      t ∉ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀) →
      ((tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)
        * (evalSeriesGen Ω₁ ((ambTheta F) ^ (Nat.card F) ^ j)) ^ (w₀ - tmWeight t.1)) = 0 := by
    intro t _ ht
    have hne : tmWeight t.1 ≠ w₀ := fun h => ht (Finset.mem_filter.mpr ⟨Finset.mem_univ t, h⟩)
    have hlt : tmWeight t.1 < w₀ := lt_of_le_of_ne (hw₀ t) hne
    rw [hΩ1 j hj, zero_pow (by omega : w₀ - tmWeight t.1 ≠ 0), mul_zero]
  have hpt : ∀ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
      (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)
      = (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)
        * (evalSeriesGen Ω₁ ((ambTheta F) ^ (Nat.card F) ^ j)) ^ (w₀ - tmWeight t.1) := by
    intro t ht
    have hwt : tmWeight t.1 = w₀ := (Finset.mem_filter.mp ht).2
    rw [hwt, Nat.sub_self, pow_zero, mul_one]
  rw [show (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
        (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
          * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j))
      = ∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
        ((tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
        * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)
        * (evalSeriesGen Ω₁ ((ambTheta F) ^ (Nat.card F) ^ j)) ^ (w₀ - tmWeight t.1))
      from Finset.sum_congr rfl hpt]
  rw [Finset.sum_subset (Finset.filter_subset _ _) hzero]
  exact hlead2

end EvalStep

/-! ## §7. The Step-2 frontier: the leading-weight MZ relation

`gSuperEntire_tmL` and `tmL_frobenius_pow` supply the two analytic inputs of
`tmB_eval_zero` (`hLse` and `hMZ`); `tmABP_a_leading` packages the whole of Dac §5.2 Step 2 up
to the relation whose coefficients must be shown to vanish.
-/

section Glue

variable {w : ℕ} {ω : PowerSeries (Ambient F)} {γ : ℚᵐ⁰}
variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- `tmL` is super-entire (Chang 5.3.1 for the `L`-series of a tuple of `I`). -/
lemma gSuperEntire_tmL (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (t : ↥(tmI S)) : GSuperEntire γ (tmL (Nat.card F) ω t.1) := by
  rw [tmL]
  refine gSuperEntire_atLrPaperGen hγ harch hq hω hωse ?_ ?_
  · intro x hx
    rw [tmCoe, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨s, hs, hy'⟩ := mem_tmI_entry F t.2 hy
    exact hsm s hs y hy'
  · intro x hx
    rw [tmCoe, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨s, hs, hy'⟩ := mem_tmI_entry F t.2 hy
    exact hSse s hs y hy'

/-- **The MZ property for `tmL`** (Chang Lemma 5.3.5 / CPY19 Prop. 2.3.3). -/
lemma tmL_frobenius_pow (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (t : ↥(tmI S)) (k : ℕ) :
    evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
      = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k) := by
  rcases List.eq_nil_or_concat t.1 with h | ⟨u, x, h⟩
  · rw [h, tmL_nil]; simp
  · have hcoe : tmCoe (K := Ambient F) (u.concat x)
        = tmCoe (K := Ambient F) u ++ [(x.1, (x.2 : PowerSeries (Ambient F)))] := by
      rw [List.concat_eq_append, tmCoe_append]
      congr 1
    rw [h, tmL, hcoe]
    have hx : x ∈ t.1 := by
      rw [h, List.concat_eq_append]
      exact List.mem_append_right _ (List.mem_singleton_self x)
    obtain ⟨sx, hsx, hx'⟩ := mem_tmI_entry F t.2 hx
    refine evalSeriesGen_atLrPaperGen_frobenius_pow (K := Ambient F) (q := Nat.card F)
      (Q := (x.2 : PowerSeries (Ambient F))) hγ0 hγ harch hq hω hωse (tmCoe u) ?_ ?_ x.1 ?_ ?_ ?_ hc k
    · intro y hy
      rw [tmCoe, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' : z ∈ t.1 := by
        rw [h, List.concat_eq_append]
        exact List.mem_append_left _ hz
      obtain ⟨s, hs, hz''⟩ := mem_tmI_entry F t.2 hz'
      exact hsm s hs z hz''
    · intro y hy
      rw [tmCoe, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' : z ∈ t.1 := by
        rw [h, List.concat_eq_append]
        exact List.mem_append_left _ hz
      obtain ⟨s, hs, hz''⟩ := mem_tmI_entry F t.2 hz'
      exact hSse s hs z hz''
    · exact hpos sx hsx x hx'
    · exact hsm sx hsx x hx'
    · exact hSse sx hsx x hx'

end Glue

section Glue2

variable {w : ℕ} {ω : PowerSeries (Ambient F)} {γ : ℚᵐ⁰}
variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- **Dac §5.2, Step 2 down to the leading-weight relation.**  From the data of Theorem 2.4 with
`f_∅(θ) + a(θ) = 0` one gets the polynomial row vector `P` of the ABP criterion *and* the
leading-weight MZ relation `∑_{t : tmWeight t = w₀} B̃_t(θ^{q^j})·(𝓛(t)(θ))^{q^j} = 0`. -/
theorem tmABP_a_leading {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F) {w : ℕ} {ω : PowerSeries (Ambient F)} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (hω0 : ω.coeff 0 ≠ 0)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) ω w S cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0)
    {w₀ : ℕ} (hw₀ : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w₀) (hw₀le : w₀ ≤ w) :
    ∃ P : Option ↥(tmI S) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * tmPsiColA F ω w S cf h0 a j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F S j) ∧
      (∀ j : ℕ, 2 ≤ j →
        (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
          (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
            * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)) = 0) := by
  classical
  obtain ⟨P, hP, hPθ⟩ :=
    tmABP_a F hγ0 hγ harch hq hω hωse hωfe hw hcf hsm hSse hne h0 hA ha hval
  refine ⟨P, hP, hPθ, ?_⟩
  have hfe : tmPsiColA F ω w S cf h0 a
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) := by
    have hfun := tmPsiColA_functional F (w := w) (ω := ω) (cf := cf) (a := a) hγ harch hq hω
      hωfe hw hcf hsm hne h0 hA ha
    rw [tmPhi_twist_mat F _ hA] at hfun
    exact hfun
  have hΩ0 : (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω).coeff 0 ≠ 0 := by
    rw [frobTwist_coeff, pow_one]
    exact pow_ne_zero _ hω0
  have hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0 := by
    intro j hj
    have hq1 : ((ambTheta F) ^ (Nat.card F ^ (j - 1))) ^ (Nat.card F ^ 1)
        = (ambTheta F) ^ (Nat.card F) ^ j := by
      rw [pow_one, ← pow_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ j by omega)]
      rw [pow_succ]
    have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) hωse
      ((ambTheta F) ^ (Nat.card F ^ (j - 1))) 1
    rw [hq1] at h
    have h2 : evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ (j - 1))) = 0 :=
      hc (j - 1) (by omega)
    rw [h2] at h
    have hz : (0 : Ambient F) ^ (Nat.card F ^ 1) = 0 :=
      zero_pow (pow_ne_zero 1 (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))
    rw [hz] at h
    exact h
  have hMZ : ∀ (t : ↥(tmI S)) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k) :=
    fun t k => tmL_frobenius_pow F hγ0 hγ harch hq hω hωse hsm hSse hpos hc t k
  have hLse : ∀ t : ↥(tmI S), GSuperEntire γ (tmL (Nat.card F) ω t.1) :=
    fun t => gSuperEntire_tmL F hγ harch hq hω hωse hsm hSse t
  exact tmB_eval_zero F hγ0 hγ harch hωse hΩ0 hΩ1 hMZ hLse h0 hA hfe hP hw₀ hw₀le

end Glue2

end ZagierHoffmanPositiveChar
