import Mathlib
import Submission.Work.WilG4a.domLociAlt
import Submission.Work.WilG4a.sliceDiff_mem

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

/-! ## 1. The point `(z,s,ε,δ,x',s')` of `ℝ^{p+6}` and its coordinates -/

/-- The point `(z,s,ε,δ,x',s')` of `ℝ^{p+6}`. -/
def Wp (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) : Fin (p + 6) → ℝ :=
  let t1 : Fin (p + 2) → ℝ := Fin.snoc z s
  let t2 : Fin (p + 3) → ℝ := Fin.snoc t1 ε
  let t3 : Fin (p + 4) → ℝ := Fin.snoc t2 δ
  let t4 : Fin (p + 5) → ℝ := Fin.snoc t3 x'
  Fin.snoc t4 s'

@[simp] theorem Wp_cX (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' (cX p) = z (Fin.last p) := by
  have h : cX p = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last p))))) :=
    Fin.ext (by simp [cX])
  rw [h]; simp only [Wp, Fin.snoc_castSucc]

@[simp] theorem Wp_cS (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' (cS p) = s := by
  have h : cS p = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last (p + 1))))) :=
    Fin.ext (by simp [cS])
  rw [h]; simp only [Wp, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] theorem Wp_cE (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' (cE p) = ε := by
  have h : cE p = Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last (p + 2)))) :=
    Fin.ext (by simp [cE])
  rw [h]; simp only [Wp, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] theorem Wp_cD (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' (cD p) = δ := by
  have h : cD p = Fin.castSucc (Fin.castSucc (Fin.last (p + 3))) := Fin.ext (by simp [cD])
  rw [h]; simp only [Wp, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] theorem Wp_cP (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' (cP p) = x' := by
  have h : cP p = Fin.castSucc (Fin.last (p + 4)) := Fin.ext (by simp [cP])
  rw [h]; simp only [Wp, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] theorem Wp_cSP (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' (cSP p) = s' := by
  have h : cSP p = Fin.last (p + 5) := Fin.ext (by simp [cSP])
  rw [h]; simp only [Wp, Fin.snoc_last]

theorem Wp_contA (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' ∘ iotaContA p = Fin.snoc z s := by
  funext j
  simp only [Function.comp_apply, iotaContA]
  have h : (Fin.castAdd 4 j : Fin (p + 6)) =
      Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc j))) := Fin.ext rfl
  rw [h]
  simp only [Wp, Fin.snoc_castSucc]

theorem Wp_contB (p : ℕ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' ∘ iotaContB p = Fin.snoc (Fin.snoc (Fin.init z) x') s' := by
  funext j
  simp only [Function.comp_apply]
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j' with ⟨j'', rfl⟩ | rfl
    · have h1 : iotaContB p (Fin.castSucc (Fin.castSucc j'')) = Fin.castAdd 6 j'' := by
        simp [iotaContB, Fin.lastCases_castSucc]
      have h2 : (Fin.castAdd 6 j'' : Fin (p + 6)) =
          Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.castSucc j''))))) :=
        Fin.ext rfl
      rw [h1, h2]
      simp only [Wp, Fin.snoc_castSucc, Fin.init]
    · have h1 : iotaContB p (Fin.castSucc (Fin.last p)) = cP p := by
        simp [iotaContB, Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [h1]
      have h2 : cP p = Fin.castSucc (Fin.last (p + 4)) := Fin.ext (by simp [cP])
      rw [h2]
      simp only [Wp, Fin.snoc_castSucc, Fin.snoc_last]
  · have h1 : iotaContB p (Fin.last (p + 1)) = cSP p := by
      simp [iotaContB, Fin.lastCases_last]
    rw [h1]
    have h2 : cSP p = Fin.last (p + 5) := Fin.ext (by simp [cSP])
    rw [h2]
    simp only [Wp, Fin.snoc_last]

/-- `Fin.snoc (Fin.init z) x' = Function.update z (Fin.last p) x'`. -/
theorem update_eq_snoc_init (w : Fin (p + 1) → ℝ) (x' : ℝ) :
    Function.update w (Fin.last p) x' = Fin.snoc (Fin.init w) x' := by
  nth_rewrite 1 [← Fin.snoc_init_self w]
  exact Fin.update_snoc_last (w (Fin.last p)) (Fin.init w) x'

theorem snoc_init_eq_update (z : Fin (p + 1) → ℝ) (x' : ℝ) :
    Fin.snoc (Fin.init z) x' = Function.update z (Fin.last p) x' :=
  (update_eq_snoc_init z x').symm

theorem snoc_at_last {n : ℕ} (f : Fin n → ℝ) (a : ℝ) (h : n < n + 1) :
    (Fin.snoc f a : Fin (n + 1) → ℝ) ⟨n, h⟩ = a := by
  rw [show (⟨n, h⟩ : Fin (n + 1)) = Fin.last n from rfl, Fin.snoc_last]

theorem sq_lt_sq_abs_y {a δ : ℝ} (hδ : 0 < δ) : a ^ 2 < δ ^ 2 ↔ |a| < δ := by
  rw [sq_lt_sq, abs_of_pos hδ]

/-! ## 2. `Ω`-bookkeeping -/

private theorem inter_poly {S : SOMin} {n : ℕ} {a₁ a₂ : ℕ} {b₁ b₂ : Polynomial ℕ} {D : ℕ}
    {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a₁ (b₁.eval D) n) (hY : Y ∈ S.Ω a₂ (b₂.eval D) n) :
    X ∩ Y ∈ S.Ω (max a₁ a₂ + 1) ((b₁ + b₂).eval D) n := by
  have hX' : X ∈ S.Ω (max a₁ a₂) (b₁.eval D) n :=
    Work.WilG1.Omega.mono hX (le_max_left a₁ a₂) le_rfl
  have hY' : Y ∈ S.Ω (max a₁ a₂) (b₂.eval D) n :=
    Work.WilG1.Omega.mono hY (le_max_right a₁ a₂) le_rfl
  have h := Work.WilG1.Plumb.inter_same hX' hY'
  simpa only [Polynomial.eval_add] using h

private theorem union_poly {S : SOMin} {n : ℕ} {a₁ a₂ : ℕ} {b₁ b₂ : Polynomial ℕ} {D : ℕ}
    {X Y : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω a₁ (b₁.eval D) n) (hY : Y ∈ S.Ω a₂ (b₂.eval D) n) :
    X ∪ Y ∈ S.Ω (max a₁ a₂) ((b₁ + b₂).eval D) n := by
  have hX' : X ∈ S.Ω (max a₁ a₂) (b₁.eval D) n :=
    Work.WilG1.Omega.mono hX (le_max_left a₁ a₂) le_rfl
  have hY' : Y ∈ S.Ω (max a₁ a₂) (b₂.eval D) n :=
    Work.WilG1.Omega.mono hY (le_max_right a₁ a₂) le_rfl
  have h := Work.WilG1.Plumb.union_same hX' hY'
  simpa only [Polynomial.eval_add] using h

/-! ## 3. The matrix `contM` -/

private theorem contM_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        contM f ∈ S.Ω a (b.eval D) (p + 6) := by
  let aD : ℕ := Work.WilG1.Plumb.AFR (p + 1) F0 + 1
  let bD : Polynomial ℕ := Polynomial.C 2 * Polynomial.X +
    Polynomial.C (2 * Work.WilG1.Plumb.KK (p + 1) + (p + 1) * 4 + 80)
  let aPre : ℕ := aD + 64 * ((p + 6) + (p + 2)) + 64
  let bPre : Polynomial ℕ := bD + Polynomial.C (32 * ((p + 6) + (p + 2)) + 32)
  let aM : ℕ := max (p + 8 + 1) (max (max aPre aPre + 1) (p + 8) + 1)
  let bM : Polynomial ℕ := Polynomial.C 4 + ((bPre + bPre) + Polynomial.C 4)
  refine ⟨aM, bM, ?_⟩
  intro D f hf
  have hDer : derSet f ∈ S.Ω aD (bD.eval D) (p + 2) :=
    derSet_memAlt S p F0 D hf
  have hPreA : Work.WilG5.coordPre (iotaContA p) (derSet f) ∈ S.Ω aPre (bPre.eval D) (p + 6) := by
    have h := Work.WilG5.coordPre_mem (S := S) (ι := iotaContA p) hDer
    simpa [aPre, bPre, aD, bD, Polynomial.eval_add, Polynomial.eval_C, Nat.add_assoc] using h
  have hPreB : Work.WilG5.coordPre (iotaContB p) (derSet f) ∈ S.Ω aPre (bPre.eval D) (p + 6) := by
    have h := Work.WilG5.coordPre_mem (S := S) (ι := iotaContB p) hDer
    simpa [aPre, bPre, aD, bD, Polynomial.eval_add, Polynomial.eval_C, Nat.add_assoc] using h
  have hL : (contLtx p)ᶜ ∈ S.Ω (p + 8 + 1) ((Polynomial.C 4).eval D) (p + 6) :=
    S.compl (contLtx_mem S p D)
  have hE : contEps p ∈ S.Ω (p + 8) ((Polynomial.C 4).eval D) (p + 6) := contEps_mem S p D
  have hAB := inter_poly hPreA hPreB
  have hABC := inter_poly hAB hE
  have hM : (contLtx p)ᶜ ∪ (Work.WilG5.coordPre (iotaContA p) (derSet f) ∩
      Work.WilG5.coordPre (iotaContB p) (derSet f) ∩ contEps p) ∈
      S.Ω aM (bM.eval D) (p + 6) :=
    union_poly hL hABC
  simpa [contM, aM, bM, aPre, bPre, aD, bD, Polynomial.eval_add, Polynomial.eval_C] using hM

/-! ## 4. The quantifier chain -/

private theorem contN1_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        contN1 f ∈ S.Ω a (b.eval D) (p + 5) := by
  obtain ⟨a, b, h⟩ := contM_mem S p F0
  refine ⟨a + 1, b, ?_⟩
  intro D f hf
  have hh : projLast (contM f) ∈ S.Ω (a + 1) (b.eval D) (p + 5) := S.proj (h D hf)
  simpa [contN1] using hh

private theorem contN2_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        contN2 f ∈ S.Ω a (b.eval D) (p + 4) := by
  obtain ⟨a, b, h⟩ := contN1_mem S p F0
  refine ⟨a + 1 + 1 + 1, b, ?_⟩
  intro D f hf
  have h1 : (contN1 f)ᶜ ∈ S.Ω (a + 1) (b.eval D) (p + 5) := S.compl (h D hf)
  have h2 : projLast ((contN1 f)ᶜ) ∈ S.Ω (a + 1 + 1) (b.eval D) (p + 4) := S.proj h1
  have h3 : (projLast ((contN1 f)ᶜ))ᶜ ∈ S.Ω (a + 1 + 1 + 1) (b.eval D) (p + 4) := S.compl h2
  simpa [contN2] using h3

private theorem contN3_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        contN3 f ∈ S.Ω a (b.eval D) (p + 3) := by
  obtain ⟨a, b, h⟩ := contN2_mem S p F0
  refine ⟨max (p + 6) a + 1 + 1, Polynomial.C 3 + b, ?_⟩
  intro D f hf
  have hpos : posHalf (p + 4) ⟨p + 3, by omega⟩ ∈
      S.Ω (p + 6) ((Polynomial.C 3).eval D) (p + 4) := posHalf_mem S (p + 4) ⟨p + 3, by omega⟩ D
  have hint : posHalf (p + 4) ⟨p + 3, by omega⟩ ∩ contN2 f ∈
      S.Ω (max (p + 6) a + 1) ((Polynomial.C 3 + b).eval D) (p + 4) := inter_poly hpos (h D hf)
  have hp : projLast (posHalf (p + 4) ⟨p + 3, by omega⟩ ∩ contN2 f) ∈
      S.Ω (max (p + 6) a + 1 + 1) ((Polynomial.C 3 + b).eval D) (p + 3) := S.proj hint
  simpa [contN3] using hp

private theorem contN4_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        contN4 f ∈ S.Ω a (b.eval D) (p + 2) := by
  obtain ⟨a, b, h⟩ := contN3_mem S p F0
  refine ⟨max (p + 5) (a + 1) + 1 + 1 + 1, Polynomial.C 3 + b, ?_⟩
  intro D f hf
  have hc : (contN3 f)ᶜ ∈ S.Ω (a + 1) (b.eval D) (p + 3) := S.compl (h D hf)
  have hpos : posHalf (p + 3) ⟨p + 2, by omega⟩ ∈
      S.Ω (p + 5) ((Polynomial.C 3).eval D) (p + 3) := posHalf_mem S (p + 3) ⟨p + 2, by omega⟩ D
  have hint : posHalf (p + 3) ⟨p + 2, by omega⟩ ∩ (contN3 f)ᶜ ∈
      S.Ω (max (p + 5) (a + 1) + 1) ((Polynomial.C 3 + b).eval D) (p + 3) := inter_poly hpos hc
  have hp : projLast (posHalf (p + 3) ⟨p + 2, by omega⟩ ∩ (contN3 f)ᶜ) ∈
      S.Ω (max (p + 5) (a + 1) + 1 + 1) ((Polynomial.C 3 + b).eval D) (p + 2) := S.proj hint
  have h3 : (projLast (posHalf (p + 3) ⟨p + 2, by omega⟩ ∩ (contN3 f)ᶜ))ᶜ ∈
      S.Ω (max (p + 5) (a + 1) + 1 + 1 + 1) ((Polynomial.C 3 + b).eval D) (p + 2) := S.compl hp
  simpa [contN4] using h3

private theorem sliceDerivContAux_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        sliceDerivContAux f ∈ S.Ω a (b.eval D) (p + 1) := by
  obtain ⟨a, b, h⟩ := contN4_mem S p F0
  refine ⟨a + 1, b, ?_⟩
  intro D f hf
  have hh : projLast (contN4 f) ∈ S.Ω (a + 1) (b.eval D) (p + 1) := S.proj (h D hf)
  simpa [sliceDerivContAux] using hh

/-! ## 5. The characterisations of the quantifier chain -/

theorem mem_contN1 (f : (Fin p → ℝ) → ℝ → ℝ) (w5 : Fin (p + 5) → ℝ) :
    w5 ∈ contN1 f ↔ ∃ s' : ℝ, Fin.snoc w5 s' ∈ contM f := Iff.rfl

theorem mem_contN2 (f : (Fin p → ℝ) → ℝ → ℝ) (w4 : Fin (p + 4) → ℝ) :
    w4 ∈ contN2 f ↔ ∀ x' : ℝ, Fin.snoc w4 x' ∈ contN1 f := by
  have key : w4 ∈ contN2 f ↔ ¬ ∃ x' : ℝ, Fin.snoc w4 x' ∈ (contN1 f)ᶜ := Iff.rfl
  rw [key]
  constructor
  · intro h x'
    by_contra hc
    exact h ⟨x', hc⟩
  · rintro h ⟨x', hc⟩
    exact hc (h x')

theorem mem_contN3 (f : (Fin p → ℝ) → ℝ → ℝ) (w3 : Fin (p + 3) → ℝ) :
    w3 ∈ contN3 f ↔ ∃ δ : ℝ, 0 < δ ∧ Fin.snoc w3 δ ∈ contN2 f := by
  have key : w3 ∈ contN3 f ↔ ∃ δ : ℝ, Fin.snoc w3 δ ∈
      posHalf (p + 4) ⟨p + 3, by omega⟩ ∧ Fin.snoc w3 δ ∈ contN2 f := Iff.rfl
  rw [key]
  constructor
  · rintro ⟨δ, h1, h2⟩
    refine ⟨δ, ?_, h2⟩
    have h := h1
    simp only [posHalf, Set.mem_ofPred_eq] at h
    rwa [snoc_at_last w3 δ] at h
  · rintro ⟨δ, h1, h2⟩
    refine ⟨δ, ?_, h2⟩
    have h := h1
    simp only [posHalf, Set.mem_ofPred_eq]
    rwa [snoc_at_last w3 δ]

theorem mem_contN4 (f : (Fin p → ℝ) → ℝ → ℝ) (w2 : Fin (p + 2) → ℝ) :
    w2 ∈ contN4 f ↔ ∀ ε : ℝ, 0 < ε → Fin.snoc w2 ε ∈ contN3 f := by
  have key : w2 ∈ contN4 f ↔ ¬ ∃ ε : ℝ, Fin.snoc w2 ε ∈
      posHalf (p + 3) ⟨p + 2, by omega⟩ ∧ Fin.snoc w2 ε ∈ (contN3 f)ᶜ := Iff.rfl
  rw [key]
  constructor
  · intro h ε hε
    by_contra hc
    refine h ⟨ε, ?_, hc⟩
    simp only [posHalf, Set.mem_ofPred_eq]
    rwa [snoc_at_last w2 ε]
  · rintro h ⟨ε, hε, hc⟩
    have hε' : 0 < ε := by
      have h := hε
      simp only [posHalf, Set.mem_ofPred_eq] at h
      rwa [snoc_at_last w2 ε] at h
    exact hc (h ε hε')

theorem mem_sliceDerivContAux (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p + 1) → ℝ) :
    z ∈ sliceDerivContAux f ↔ ∃ s : ℝ, Fin.snoc z s ∈ contN4 f := Iff.rfl

theorem mem_contM (f : (Fin p → ℝ) → ℝ → ℝ) (z : Fin (p + 1) → ℝ) (s ε δ x' s' : ℝ) :
    Wp p z s ε δ x' s' ∈ contM f ↔
      ¬((x' - z (Fin.last p)) ^ 2 < δ ^ 2) ∨
        (IsSliceDeriv f z s ∧ IsSliceDeriv f (Function.update z (Fin.last p) x') s' ∧
          (s' - s) ^ 2 < ε ^ 2) := by
  have hL : Wp p z s ε δ x' s' ∈ contLtx p ↔ (x' - z (Fin.last p)) ^ 2 < δ ^ 2 := by
    simp only [contLtx, Set.mem_ofPred_eq, Wp_cP, Wp_cX, Wp_cD]
  have hA : Wp p z s ε δ x' s' ∈ Work.WilG5.coordPre (iotaContA p) (derSet f) ↔
      IsSliceDeriv f z s := by
    simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq, Wp_contA, mem_derSet, Fin.init_snoc,
      Fin.snoc_last]
  have hB : Wp p z s ε δ x' s' ∈ Work.WilG5.coordPre (iotaContB p) (derSet f) ↔
      IsSliceDeriv f (Function.update z (Fin.last p) x') s' := by
    simp only [Work.WilG5.coordPre, Set.mem_ofPred_eq, Wp_contB, mem_derSet, Fin.init_snoc,
      Fin.snoc_last, snoc_init_eq_update]
  have hE : Wp p z s ε δ x' s' ∈ contEps p ↔ (s' - s) ^ 2 < ε ^ 2 := by
    simp only [contEps, Set.mem_ofPred_eq, Wp_cSP, Wp_cS, Wp_cE]
  have hcpl : (Wp p z s ε δ x' s' ∈ (contLtx p)ᶜ) ↔
      ¬(Wp p z s ε δ x' s' ∈ contLtx p) := Iff.rfl
  rw [contM, Set.mem_union, hcpl, hL, Set.mem_inter_iff, Set.mem_inter_iff, hA, hB, hE]
  simp only [and_assoc]

/-! ## 6. The identity `sliceDerivContAux = sliceDerivCont` -/

theorem sliceDerivContAux_eq (f : (Fin p → ℝ) → ℝ → ℝ) :
    sliceDerivContAux f = sliceDerivCont f := by
  ext z
  rw [(mem_sliceDerivContAux f z), sliceDerivCont]
  constructor
  · rintro ⟨s, hs⟩
    have hz : IsSliceDeriv f z s := by
      have h1 : Fin.snoc (Fin.snoc z s) 1 ∈ contN3 f :=
        (mem_contN4 f (Fin.snoc z s)).mp hs 1 (by norm_num)
      obtain ⟨δ, hδ, h2⟩ := (mem_contN3 f (Fin.snoc (Fin.snoc z s) 1)).mp h1
      obtain ⟨s', h4⟩ := (mem_contN1 f _).mp
        ((mem_contN2 f _).mp h2 (z (Fin.last p)))
      rcases (mem_contM f z s 1 δ (z (Fin.last p)) s').mp h4 with h5 | ⟨h5, -, -⟩
      · exact absurd (by
          have h6 : ((z (Fin.last p) : ℝ) - z (Fin.last p)) ^ 2 = 0 := by ring
          rw [h6]; positivity) h5
      · exact h5
    refine ⟨s, hz, fun ε hε => ?_⟩
    have h1 : Fin.snoc (Fin.snoc z s) ε ∈ contN3 f :=
      (mem_contN4 f (Fin.snoc z s)).mp hs ε hε
    obtain ⟨δ, hδ, h2⟩ := (mem_contN3 f (Fin.snoc (Fin.snoc z s) ε)).mp h1
    refine ⟨δ, hδ, fun x' hx' => ?_⟩
    obtain ⟨s', h4⟩ := (mem_contN1 f _).mp ((mem_contN2 f _).mp h2 x')
    rcases (mem_contM f z s ε δ x' s').mp h4 with h5 | ⟨-, h5, h6⟩
    · exact absurd ((sq_lt_sq_abs_y hδ).mpr hx') h5
    · exact ⟨s', h5, (sq_lt_sq_abs_y hε).mp h6⟩
  · rintro ⟨s, hs, hcont⟩
    refine (mem_sliceDerivContAux f z).mpr ⟨s, ?_⟩
    refine (mem_contN4 f (Fin.snoc z s)).mpr (fun ε hε => ?_)
    obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
    refine (mem_contN3 f (Fin.snoc (Fin.snoc z s) ε)).mpr ⟨δ, hδ, ?_⟩
    refine (mem_contN2 f _).mpr (fun x' => ?_)
    by_cases hx : |x' - z (Fin.last p)| < δ
    · obtain ⟨s', hs', hclose⟩ := hδ' x' hx
      refine (mem_contN1 f _).mpr ⟨s', (mem_contM f z s ε δ x' s').mpr (Or.inr ⟨hs, hs', ?_⟩)⟩
      exact (sq_lt_sq_abs_y hε).mpr hclose
    · refine (mem_contN1 f _).mpr ⟨0, (mem_contM f z s ε δ x' 0).mpr (Or.inl ?_)⟩
      intro hcon
      exact hx ((sq_lt_sq_abs_y hδ).mp hcon)

/-! ## 7. The theorem -/

/-- **`Ω`-membership of `sliceDerivCont`.** -/
theorem sliceDerivCont_memAlt (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        Work.WilG4a.sliceDerivCont f ∈ S.Ω a (b.eval D) (p + 1) := by
  obtain ⟨a, b, h⟩ := sliceDerivContAux_mem S p F0
  refine ⟨a, b, ?_⟩
  intro D f hf
  rw [← sliceDerivContAux_eq f]
  exact h D hf

end Work.WilG4a
