import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.span_mono
import Submission.Work.BW.eval_conePt_mono
import Submission.Work.BW.boxPts_eq_Icc
import Submission.Work.BW.mono_mem_homPiece

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Definitions and interface lemmas for `Work.BW.finrank_subIdeal_false`

The Hilbert function of the coordinate ring of the closure of `G' = {0} × ker 𝒵` in multidegree
`d` is computed by choosing one representative monomial per class of the torus box
`∏ᵢ [0, d_{i+1}]` modulo the lattice `𝒵 = rowLat M`.  This file sets up that box, the classes,
the chosen representatives, the corresponding monomials `xmono`, and the graded piece
`subPiece` of the vanishing ideal `subIdeal N ρ false M`, together with the small interface
lemmas needed by the two halves of the proof (independence and spanning).
-/

namespace Work.BW

open MvPolynomial

noncomputable section

/-- The torus box multidegree `(d_{i+1})_i`. -/
def mBox {N : ℕ} (d : Fin (N + 1) →₀ ℕ) : Fin N → ℕ := fun i => d i.succ

/-- The set of classes modulo `𝒵 = rowLat M` of the lattice points of the torus box
`∏ᵢ [0, d_{i+1}]`; its cardinality is `boxClassCount N ρ M (fun i => d i.succ)`. -/
noncomputable def clsSet {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ) :
    Finset ((Fin N → ℤ) ⧸ rowLat N ρ M) := by
  classical
  exact (boxPts N (mBox d)).image
    (fun b => (Submodule.Quotient.mk b : (Fin N → ℤ) ⧸ rowLat N ρ M))

/-- A representative lattice point of the box for a realized class. -/
noncomputable def repPt {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : Fin N → ℤ := by
  classical
  exact Classical.choose (Finset.mem_image.mp c.2)

lemma repPt_mem {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : repPt d M c ∈ boxPts N (mBox d) := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp c.2)).1

lemma repPt_cls {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) :
    (Submodule.Quotient.mk (repPt d M c) : (Fin N → ℤ) ⧸ rowLat N ρ M) = c.1 := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp c.2)).2

lemma repPt_mem_Icc {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) :
    repPt d M c ∈ Finset.Icc (0 : Fin N → ℤ) (fun i => ((mBox d) i : ℤ)) := by
  rw [← boxPts_eq_Icc]
  exact repPt_mem d M c

lemma repPt_nonneg {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) (i : Fin N) : 0 ≤ repPt d M c i :=
  (Finset.mem_Icc.mp (repPt_mem_Icc d M c)).1 i

lemma repPt_le {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) (i : Fin N) : repPt d M c i ≤ (d i.succ : ℤ) :=
  (Finset.mem_Icc.mp (repPt_mem_Icc d M c)).2 i

/-- The exponent vector `(0, (repPt)ᵢ)` in the box `{b ∈ degBox N d | b 0 = 0}` attached to a
realized class. -/
noncomputable def repExp {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : Fin (N + 1) → ℕ :=
  Fin.cons 0 (fun i => (repPt d M c i).toNat)

@[simp] lemma repExp_zero {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : repExp d M c 0 = 0 := rfl

lemma repExp_succ {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) (i : Fin N) : repExp d M c i.succ = (repPt d M c i).toNat := by
  rw [repExp, Fin.cons_succ]

lemma repExp_le {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) (i : Fin (N + 1)) : repExp d M c i ≤ d i := by
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    rw [repExp_succ]
    exact Int.toNat_le.mpr (repPt_le d M c j)

lemma torPart_repExp {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : torPart (repExp d M c) = repPt d M c := by
  funext i
  show ((repExp d M c) i.succ : ℤ) = repPt d M c i
  rw [repExp_succ]
  exact Int.toNat_of_nonneg (repPt_nonneg d M c i)

lemma clsOf_torPart_repExp {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : clsOf N ρ M (torPart (repExp d M c)) = c.1 := by
  rw [clsOf, torPart_repExp, repPt_cls]

/-- The monomial attached to a realized class, as an element of `homPiece N d`. -/
noncomputable def xmono {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : homPiece N d :=
  ⟨mono N d (repExp d M c), mono_mem_homPiece N d _ (repExp_le d M c)⟩

@[simp] lemma xmono_coe {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (c : clsSet d M) : ((xmono d M c : homPiece N d) : MR N) = mono N d (repExp d M c) := rfl

/-- The graded piece `(I ⊓ homPiece N d)` of the vanishing ideal of `{0} × ker 𝒵`, as a
submodule of `homPiece N d`. -/
noncomputable def subPiece (N ρ : ℕ) (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ) :
    Submodule ℂ (homPiece N d) :=
  Submodule.comap (homPiece N d).subtype ((subIdeal N ρ false M).restrictScalars ℂ)

/-! ### Interface lemmas for the classification of the graded piece -/

/-- Elements of `subIdeal` vanish at every point of `G'`. -/
lemma subIdeal_vanish_false {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) {y : Fin (N + 1) → ℂ}
    (hy : InSub N ρ false M y) {F : MR N} (hF : F ∈ subIdeal N ρ false M) :
    MvPolynomial.eval (conePt N y) F = 0 := by
  have hle : Ideal.span {G : MR N | (∃ d, G ∈ homPiece N d) ∧
      ∀ z, InSub N ρ false M z → MvPolynomial.eval (conePt N z) G = 0} ≤
      RingHom.ker (MvPolynomial.eval (conePt N y)) := by
    rw [Ideal.span_le]
    rintro G ⟨-, hGy⟩
    exact hGy y hy
  exact hle hF

/-- For a multihomogeneous `F`, membership in `subIdeal N ρ false M` is exactly vanishing on
`G' = {0} × ker 𝒵`. -/
lemma subIdeal_mem_iff_false {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) {d : Fin (N + 1) →₀ ℕ}
    {F : MR N} (hF : F ∈ homPiece N d) :
    F ∈ subIdeal N ρ false M ↔
      ∀ y, InSub N ρ false M y → MvPolynomial.eval (conePt N y) F = 0 :=
  ⟨fun h y hy => subIdeal_vanish_false M hy h, fun h => Ideal.subset_span ⟨⟨d, hF⟩, h⟩⟩

end


/-- `X_{0,1}` vanishes at every point of `G' = {0} × ker 𝒵`, hence lies in the vanishing ideal. -/
lemma X01_mem_subIdeal_false {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) :
    (MvPolynomial.X (((0 : Fin (N + 1)), 1) : Fin (N + 1) × Fin 2) : MR N) ∈
      subIdeal N ρ false M := by
  refine Ideal.subset_span ⟨?_, ?_⟩
  · exact ⟨Finsupp.single (0 : Fin (N + 1)) 1,
      MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) _⟩
  · intro y' hy'
    rw [MvPolynomial.eval_X]
    simp [conePt, hy'.1 rfl]

/-- Any multihomogeneous monomial `mono N d b` with `b 0 ≥ 1` vanishes on `G' = {0} × ker 𝒵`,
because `X_{0,1}` does. -/
lemma mono_mem_subIdeal_of_pos {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ)
    (b : Fin (N + 1) → ℕ) (hb_le : ∀ i, b i ≤ d i) (hb : 1 ≤ b 0) :
    mono N d b ∈ subIdeal N ρ false M := by
  rw [subIdeal_mem_iff_false M (mono_mem_homPiece N d b hb_le)]
  intro y hy
  rw [eval_conePt_mono, Fin.prod_univ_succ, hy.1 rfl,
    zero_pow (by omega : b 0 ≠ 0), zero_mul]

end Work.BW
