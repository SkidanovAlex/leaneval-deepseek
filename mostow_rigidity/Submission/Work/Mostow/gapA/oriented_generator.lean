import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.gapA.stdRoot_in_finite_subgroup
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.ogAux
import Submission.Work.Mostow.gapA.ogAux2
import Submission.Work.Mostow.gapA.ogAux3

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

variable {a b : E 3}

/-- The real part of `exp (-x i)` is `cos x`. -/
lemma exp_re_eq_cos (x : ℝ) : (Complex.exp (-(x : ℂ) * Complex.I)).re = Real.cos x := by
  rw [Complex.exp_re]
  have h1 : (-(x : ℂ) * Complex.I).re = 0 := by simp
  have h2 : (-(x : ℂ) * Complex.I).im = -x := by simp
  rw [h1, h2, Real.exp_zero, one_mul, Real.cos_neg]

/-- Multiplication of the complex parameters of two rotations of the normal plane. -/
lemma zOf_mul_of_forms (hA : Submission.Mostow.POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) {c s c' s' : ℝ}
    (hgf : rotMat B g = !![c, -s; s, c]) (hhf : rotMat B h = !![c', -s'; s', c']) :
    zOf B (g * h) = zOf B g * zOf B h := by
  have hprod : rotMat B (g * h) = !![c * c' - s * s', -(c * s' + s * c');
      c * s' + s * c', c * c' - s * s'] := by
    rw [rotMat_mul hA B hg hh, hgf, hhf, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [zOf_eq_mat, hprod, zOf_eq_mat, hgf, zOf_eq_mat, hhf]
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩ <;> simp [Complex.mul_re, Complex.mul_im] <;> ring_nf

/-- Injectivity of the complex parameter on rotations of the normal plane. -/
lemma zOf_inj_of_forms (hA : Submission.Mostow.POActionProp 3) (B : PB a b) {g h : PO 3 1}
    (hg : g ∈ AxisSub hA a b) (hh : h ∈ AxisSub hA a b) {c s c' s' : ℝ}
    (hgf : rotMat B g = !![c, -s; s, c]) (hhf : rotMat B h = !![c', -s'; s', c'])
    (hz : zOf B g = zOf B h) : g = h := by
  have hc : c = c' := by
    have h := congrArg Complex.re hz
    rw [zOf_eq_mat, hgf, zOf_eq_mat, hhf] at h
    simpa using h
  have hs : s = s' := by
    have h := congrArg Complex.im hz
    rw [zOf_eq_mat, hgf, zOf_eq_mat, hhf] at h
    simpa using h
  have hmat : rotMat B g = rotMat B h := by rw [hgf, hhf, hc, hs]
  have hE : ∀ u : Submission.Mostow.E 3, emat g *ᵥ hlift u = emat h *ᵥ hlift u := by
    intro u
    obtain ⟨α, β, γ, δ, hαβγδ⟩ := B.spanV (hlift u)
    have h00 : rot00 B g = rot00 B h := by
      rw [← rotMat_apply_zero_zero (B := B) (g := g),
        ← rotMat_apply_zero_zero (B := B) (g := h), hmat]
    have h10 : rot10 B g = rot10 B h := by
      rw [← rotMat_apply_one_zero (B := B) (g := g),
        ← rotMat_apply_one_zero (B := B) (g := h), hmat]
    have h01 : rot01 B g = rot01 B h := by
      rw [← rotMat_apply_zero_one (B := B) (g := g),
        ← rotMat_apply_zero_one (B := B) (g := h), hmat]
    have h11 : rot11 B g = rot11 B h := by
      rw [← rotMat_apply_one_one (B := B) (g := g),
        ← rotMat_apply_one_one (B := B) (g := h), hmat]
    have he1 : emat g *ᵥ B.e1 = emat h *ᵥ B.e1 := by
      rw [emat_mulVec_e1 hA B hg, emat_mulVec_e1 hA B hh, h00, h10]
    have he2 : emat g *ᵥ B.e2 = emat h *ᵥ B.e2 := by
      rw [emat_mulVec_e2 hA B hg, emat_mulVec_e2 hA B hh, h01, h11]
    obtain ⟨hg1, hg2, -⟩ := mem_AxisSub_iff.mp hg
    obtain ⟨hh1, hh2, -⟩ := mem_AxisSub_iff.mp hh
    rw [hαβγδ]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hg1, hg2, hh1, hh2, he1, he2]
  have hgu : ∀ u : Submission.Mostow.E 3, g • u = h • u := by
    intro u
    have hz' := hE u
    rw [emat_hlift g u, emat_hlift h u] at hz'
    exact Submission.Mostow.Hyper.hlift_injective hz'
  have h2 : ∀ u : Submission.Mostow.E 3, (h⁻¹ * g) • u = u := by
    intro u
    rw [(POBasic.ofProp hA).mul_smul, hgu u, ← (POBasic.ofProp hA).mul_smul, inv_mul_cancel,
      (POBasic.ofProp hA).one_smul]
  have h3 : h⁻¹ * g = 1 := (POBasic.ofProp hA).faithful _ h2
  calc g = h * (h⁻¹ * g) := by group
    _ = h * 1 := by rw [h3]
    _ = h := mul_one h

theorem oriented_generator (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (f : LeanEval.Geometry.MostowRigidity.PO 3 1) (hfmem : f ∈ Γ) (hf : f ≠ 1)
    (hfin : IsOfFinOrder f) (hor : Work.Mostow.IsOriented f)
    (hax : ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → f • u = u) :
    ∃ b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1,
      b₀ ∈ Γ ∧ Work.Mostow.IsOriented b₀ ∧ IsOfFinOrder b₀ ∧
      (∀ u : Submission.Mostow.E 3, b₀ • u = u ↔ u ∈ Work.Mostow.geodSet a b) ∧
      (∃ k : ℤ, f = b₀ ^ k) ∧
      (∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1, g ∈ Γ → IsOfFinOrder g →
        (∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g • u = u) →
        (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ Work.Mostow.IsOriented g) ∧
      (∀ (k : ℕ) (Z : Fin 3 ⊕ Fin 1 → ℝ),
        Work.Mostow.mink Z (Work.Mostow.nvec a) = 0 → Work.Mostow.mink Z (Work.Mostow.nvec b) = 0 →
        Work.Mostow.mink (Matrix.mulVec ((Work.Mostow.emat b₀) ^ k) Z) Z
          = Real.cos (2 * Real.pi * (k : ℝ) / (orderOf b₀ : ℝ)) * Work.Mostow.mink Z Z) := by
  classical
  obtain ⟨B, -⟩ := pb_exists a b ha hb hab
  -- the subgroup of elements of `Γ` fixing the geodesic pointwise and orientation preserving
  let H : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1) :=
    Γ ⊓ Work.Mostow.gapA.AxisSub hA a b
  have hHΓ : H ≤ Γ := inf_le_left
  have hHA : H ≤ Work.Mostow.gapA.AxisSub hA a b := inf_le_right
  haveI hHfin : Finite ↥H := finite_inter_axisSub hA hI Γ hΓ a b ha hb hab
  haveI hHne : Nonempty ↥H := ⟨1⟩
  haveI hHft : Fintype ↥H := Fintype.ofFinite _
  -- the normal action of an element of `H` is a rotation
  have hdet : ∀ g : ↥H,
      (Work.Mostow.gapA.rotMat B (g : PO 3 1)).det = 1 :=
    fun g => rotMat_det_ogAux3 hA a b ha hb hab B (g : PO 3 1) (hHA g.2)
  have hform : ∀ g : ↥H, Work.Mostow.gapA.rotMat B (g : PO 3 1)
      = !![Work.Mostow.gapA.rot00 B (g : PO 3 1),
           -(Work.Mostow.gapA.rot10 B (g : PO 3 1));
           Work.Mostow.gapA.rot10 B (g : PO 3 1),
           Work.Mostow.gapA.rot00 B (g : PO 3 1)] := by
    intro g
    obtain ⟨h1, h2, -⟩ := rotMat_form hA B (hHA g.2) (hdet g)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rotMat, h1, h2]
  -- the homomorphism `ℂˣ` attached to the normal action
  let zHom : ↥H →* ℂˣ :=
    { toFun := fun g => Units.mk0 (zOf B (g : PO 3 1)) (zOf_ne_zero hA B (hHA g.2))
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one]
        change zOf B (1 : PO 3 1) = 1
        rw [zOf_eq_mat, rotMat_one hA B]
        apply Complex.ext <;> simp
      map_mul' := by
        intro g h
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
        exact zOf_mul_of_forms hA B (hHA g.2) (hHA h.2) (hform g) (hform h) }
  have hzinj : Function.Injective zHom := by
    intro g h hgh
    apply Subtype.ext
    refine zOf_inj_of_forms hA B (hHA g.2) (hHA h.2) (hform g) (hform h) ?_
    have h' := congrArg (fun u : ℂˣ => (u : ℂ)) hgh
    simpa [zHom, Units.val_mk0] using h'
  -- the range is a finite subgroup of `ℂˣ`
  let G : Subgroup ℂˣ := MonoidHom.range zHom
  have hcardG : Nat.card ↥G = Nat.card ↥H := by
    have hb : Function.Bijective
        (fun g : ↥H => (⟨zHom g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : ↥G)) := by
      refine ⟨?_, ?_⟩
      · intro g h hgh
        exact hzinj (Subtype.ext_iff.mp hgh)
      · intro z
        obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp z.2
        exact ⟨g, Subtype.ext hg⟩
    exact (Nat.card_congr (Equiv.ofBijective _ hb)).symm
  have hnposH : 0 < Nat.card ↥H := Nat.card_pos
  haveI hGfin : Finite ↥G :=
    Nat.finite_of_card_ne_zero (by rw [hcardG]; exact hnposH.ne')
  have hle : G ≤ rootsOfUnity (Nat.card ↥H) ℂ := by
    rintro z ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    have h1 : g ^ Nat.card ↥H = 1 := pow_card_eq_one'
    have h2 := congrArg (fun u : ↥H => zHom u) h1
    simp only [map_pow, map_one] at h2
    exact h2
  -- a generator of `G`
  obtain ⟨z₀, hz₀G, hz₀exp⟩ := stdRoot_in_finite_subgroup G hGfin
  rw [hcardG] at hz₀exp
  obtain ⟨u₀, hu₀⟩ := MonoidHom.mem_range.mp hz₀G
  let b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1 := (u₀ : PO 3 1)
  have hnpos : 0 < Nat.card ↥H := hnposH
  have hGzp : G = Subgroup.zpowers z₀ :=
    zpowers_eq_of_card (Nat.card ↥H) hnpos G hcardG hle z₀ hz₀G hz₀exp
  have hzord : orderOf z₀ = Nat.card ↥H := orderOf_exp_neg _ hnpos z₀ hz₀exp
  -- `H` is generated by `b₀`
  have hHzp : H = Subgroup.zpowers b₀ := by
    refine le_antisymm ?_ ?_
    · intro g hg
      have hzg : zHom ⟨g, hg⟩ ∈ Subgroup.zpowers z₀ := by
        rw [← hGzp]
        exact MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzg
      have hkg : (⟨g, hg⟩ : ↥H) = u₀ ^ k := hzinj (by rw [map_zpow, hu₀, hk])
      have hcoe : g = b₀ ^ k := by
        have h' := congrArg (fun x : ↥H => (x : PO 3 1)) hkg
        simpa [b₀, Subgroup.coe_zpow] using h'
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hcoe.symm⟩
    · intro g hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← hk]
      exact H.zpow_mem u₀.2 k
  have hord_u : orderOf u₀ = Nat.card ↥H := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one]
      exact pow_card_eq_one'
    · rw [← hzord, orderOf_dvd_iff_pow_eq_one]
      rw [show z₀ ^ orderOf u₀ = zHom (u₀ ^ orderOf u₀) by rw [map_pow, hu₀],
        pow_orderOf_eq_one, map_one]
  have hord : orderOf b₀ = Nat.card ↥H := by
    rw [show b₀ = (u₀ : PO 3 1) from rfl, Subgroup.orderOf_coe]
    exact hord_u
  -- `f` lies in `H`
  have hfH : f ∈ H :=
    ⟨hfmem, mem_AxisSub_of_isOriented_of_fixes hA hI ha hb hab hor hax⟩
  have hn2 : 2 ≤ Nat.card ↥H := by
    have hne : (1 : ↥H) ≠ ⟨f, hfH⟩ := by
      intro h
      exact hf (congrArg (fun g : ↥H => (g : PO 3 1)) h).symm
    have hcard : ({1, (⟨f, hfH⟩ : ↥H)} : Finset ↥H).card = 2 := Finset.card_pair hne
    rw [Nat.card_eq_fintype_card]
    calc 2 = ({1, (⟨f, hfH⟩ : ↥H)} : Finset ↥H).card := hcard.symm
      _ ≤ Fintype.card ↥H := Finset.card_le_univ _
  -- the value of `rot00` at `b₀`
  have hz₀u₀ : zOf B b₀ = (z₀ : ℂ) := by
    have h' := congrArg (fun u : ℂˣ => (u : ℂ)) hu₀
    simpa [zHom, Units.val_mk0] using h'
  have hnR : (0 : ℝ) < (Nat.card ↥H : ℝ) := by exact_mod_cast hnpos
  have hrot00 : Work.Mostow.gapA.rot00 B b₀
      = Real.cos (2 * Real.pi / (Nat.card ↥H : ℝ)) := by
    rw [show Work.Mostow.gapA.rot00 B b₀ = (zOf B b₀).re from rfl, hz₀u₀, hz₀exp]
    simpa using exp_re_eq_cos (2 * Real.pi / (Nat.card ↥H : ℝ))
  have hpi2 : 2 * Real.pi / (Nat.card ↥H : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hnR]
    have h2 : (2 : ℝ) ≤ (Nat.card ↥H : ℝ) := by exact_mod_cast hn2
    nlinarith [Real.pi_pos]
  have hc1 : Work.Mostow.gapA.rot00 B b₀ ≠ 1 := by
    rw [hrot00]
    refine ne_of_lt ?_
    have hpos : 0 < 2 * Real.pi / (Nat.card ↥H : ℝ) := by positivity
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hpi2 hpos
    simpa using hlt
  -- the fixed set of `b₀` is exactly the geodesic
  have hfix : ∀ u : Submission.Mostow.E 3, b₀ • u = u ↔ u ∈ Work.Mostow.geodSet a b := by
    intro u
    constructor
    · intro hu
      refine fixed_mem_geodSet hA hI a b ha hb hab B b₀ (hHA u₀.2)
        (Work.Mostow.gapA.rot00 B b₀) hc1 ?_ hu
      intro Z hZa hZb
      exact mink_mulVec_zOf hA B (hHA u₀.2) (hform u₀) (mem_NormP.mpr ⟨hZa, hZb⟩)
    · intro hu
      exact geodSet_fixed_of_mem_AxisSub hA ha hb hab (hHA u₀.2) u hu
  -- the rotation formula
  have hrot : ∀ (k : ℕ) (Z : Fin 3 ⊕ Fin 1 → ℝ),
      Work.Mostow.mink Z (Work.Mostow.nvec a) = 0 → Work.Mostow.mink Z (Work.Mostow.nvec b) = 0 →
      Work.Mostow.mink (Matrix.mulVec ((Work.Mostow.emat b₀) ^ k) Z) Z
        = Real.cos (2 * Real.pi * (k : ℝ) / (orderOf b₀ : ℝ)) * Work.Mostow.mink Z Z := by
    intro k Z hZa hZb
    have hZ : Z ∈ NormP a b := mem_NormP.mpr ⟨hZa, hZb⟩
    have hzk : (zOf B b₀) ^ k
        = Complex.exp (-((2 * Real.pi * (k : ℝ) / (Nat.card ↥H : ℝ) : ℝ) : ℂ) * Complex.I) := by
      rw [hz₀u₀, hz₀exp, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring_nf
    have hpow : Work.Mostow.mink (Matrix.mulVec (Work.Mostow.emat (b₀ ^ k)) Z) Z
        = ((zOf B b₀) ^ k).re * Work.Mostow.mink Z Z :=
      mink_pow hA B (hHA u₀.2) (hform u₀) k hZ
    rw [← emat_pow hA b₀ k, hpow, hzk, exp_re_eq_cos, ← hord]
  refine ⟨b₀, hHΓ u₀.2, isOriented_of_mem_AxisSub (hHA u₀.2),
    orderOf_pos_iff.mp (by rw [hord]; exact hnpos), hfix, ?_, ?_, hrot⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hHzp]; exact hfH)
    exact ⟨k, hk.symm⟩
  · intro g hgΓ hgfin hgax
    by_cases hgor : Work.Mostow.IsOriented g
    · left
      have hgH : g ∈ H :=
        ⟨hgΓ, mem_AxisSub_of_isOriented_of_fixes hA hI ha hb hab hgor hgax⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hHzp]; exact hgH)
      exact ⟨k, hk.symm⟩
    · exact Or.inr hgor

end

end Work.Mostow.gapA
