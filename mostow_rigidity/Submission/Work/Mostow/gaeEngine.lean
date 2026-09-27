import Mathlib
import Submission.Work.Mostow.gaeTube
import Submission.Work.Mostow.gaeFD
import Submission.Work.Mostow.ftbPivotDefs
import Submission.Work.Mostow.rotCanonEqRotN
import Submission.Work.Mostow.even_normal_dim
import Submission.Work.Mostow.conj_fundamentalDomain
import Submission.Work.Mostow.KMcovol
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.rotCanonAux
import Submission.Work.Mostow.nearIdAt_conj
import Submission.Work.Mostow.geeBlkFixStd
import Submission.Work.Mostow.boundedTorsionAux

/-!
# `gaeEngine`: the finite-type tube engine for even `n ≥ 4` (independent second proof)

The statement of `Work.Mostow.finTypeTubeEven`, proved without importing that file:
`gaeTubeEven n` is the uniform covolume bound `ofReal (c * η ^ (-α)) ≤ volH n D` (with `α > 0`)
for a discrete `Λ` with fundamental domain `D` whose near-group `nearGrp Λ z η` is finite and
non-trivial.

Route.  `Work.Mostow.ftbPivotDefs` produces a pivot `b ∈ Λ ∖ {1}` with a fixed point,
`rotCanon b ≤ C η` and the rotation separation; `elliptic_normal_form` writes `b` in block normal
form `h⁻¹ * b * h = e ▸ blk j m 1 R` with `R` fixed-point free; `rotCanon b = rotN R`
(`Work.Mostow.rotCanonEqRotN`), and conjugating `Λ`, `D`, `z` by `h` reduces the problem to the
standard stratum, where `Work.Mostow.gaeTube` (a self-contained copy of `ftbStandardTube`) gives
`ofReal (C η⁻¹) ≤ volH n D`.  `rotN R < 2` forces `Even m` (parity), hence `j ≠ 1`; the constant is
minimised over the finitely many strata `(j, m)` with `j + m = n`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

open scoped ENNReal

/-! ## Elementary helpers -/

/-- A nonzero vector exists in a positive-dimensional Euclidean space. -/
lemma gae_exists_ne_zero (m : ℕ) (hm : 1 ≤ m) : ∃ w : E m, w ≠ 0 := by
  refine ⟨EuclideanSpace.single ⟨0, hm⟩ (1 : ℝ), ?_⟩
  intro h0
  have h1 : ‖(EuclideanSpace.single ⟨0, hm⟩ (1 : ℝ) : E m)‖ = 0 := by rw [h0, norm_zero]
  have h2 : ‖(EuclideanSpace.single ⟨0, hm⟩ (1 : ℝ) : E m)‖ = 1 := by
    simpa using PiLp.norm_single 2 (fun _ : Fin m => ℝ) ⟨0, hm⟩ (1 : ℝ)
  linarith

/-- A fixed-point-free linear isometry of a positive-dimensional space is not the identity. -/
lemma gae_ne_one_of_free {m : ℕ} (hm : 1 ≤ m) {R : E m ≃ₗᵢ[ℝ] E m}
    (hR : ∀ w : E m, R w = w → w = 0) : R ≠ 1 := by
  intro h
  obtain ⟨w, hw⟩ := gae_exists_ne_zero m hm
  exact hw (hR w (by rw [h]; rfl))

/-- `rotN R = 0` only for `R = 1`. -/
lemma gae_rotN_eq_zero {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) (h : rotN R = 0) : R = 1 := by
  have h1 : ((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      - ContinuousLinearMap.id ℝ (E m)) = 0 := norm_eq_zero.mp h
  refine LinearIsometryEquiv.ext (fun x => ?_)
  have h2 := congrArg (fun f : E m →L[ℝ] E m => f x) h1
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply] at h2
  exact sub_eq_zero.mp h2

/-- An isometry that is not the identity has positive `rotN`. -/
lemma gae_rotN_pos_of_ne_one {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) (h : R ≠ 1) : 0 < rotN R := by
  rcases lt_or_eq_of_le (norm_nonneg ((R.toLinearIsometry.toContinuousLinearMap : E m →L[ℝ] E m)
      - ContinuousLinearMap.id ℝ (E m))) with hlt | heq
  · simpa only [rotN] using hlt
  · exact absurd (gae_rotN_eq_zero R heq.symm) h

/-- `NearIdAt` is monotone in the tolerance. -/
lemma gaeNearIdAt_mono {n : ℕ} {g : PO n 1} {z : E n} {η η' : ℝ}
    (h : NearIdAt g z η) (hle : η ≤ η') : NearIdAt g z η' := by
  intro u hu
  exact lt_of_lt_of_le (h u hu) hle

/-! ## `rotCanon` of a block element, and invariance under conjugation -/

/-- `rotCanon` of a block element is the rotation norm of its normal part. -/
theorem gaeRotCanonBlk {N : ℕ} (hAall : ∀ k, POActionProp k) (hIall : ∀ k, HypIsometryProp k)
    {j m : ℕ} (e : j + m = N) (B : E m ≃ₗᵢ[ℝ] E m) :
    rotCanon hAall hIall (e ▸ blk j m 1 B : PO N 1) = rotN B := by
  have hfix : ∃ p : E N, (e ▸ blk j m 1 B : PO N 1) • p = p :=
    ⟨0, rcBlk_fixes_zero e B⟩
  obtain ⟨j', m', e', hh, R, hRfree, hconj⟩ :=
    elliptic_normal_form N (hAall N) (hIall N) hAall hIall (e ▸ blk j m 1 B : PO N 1) hfix
  have h1 : rotCanon hAall hIall (e ▸ blk j m 1 B : PO N 1) = rotN R :=
    rotCanonEqRotN N hAall hIall (e ▸ blk j m 1 B : PO N 1) j' m' e' R hRfree hh hconj
  rw [h1]
  have hk' : (e' ▸ blk j' m' 1 R : PO N 1) = hh⁻¹ * (e ▸ blk j m 1 B : PO N 1) * hh :=
    hconj.symm
  exact (rcRotN_conj_blk e e' B R hh hk').symm

/-- `rotCanon` is invariant under conjugation. -/
theorem gaeRotCanonConj {N : ℕ} (hAall : ∀ k, POActionProp k) (hIall : ∀ k, HypIsometryProp k)
    (x kk : PO N 1) :
    rotCanon hAall hIall (kk⁻¹ * x * kk) = rotCanon hAall hIall x := by
  have hAb := POBasic.ofProp (hAall N)
  by_cases hx : ∃ p : E N, x • p = p
  · have hy : ∃ p : E N, (kk⁻¹ * x * kk) • p = p := by
      obtain ⟨p, hp⟩ := hx
      refine ⟨kk⁻¹ • p, ?_⟩
      have h1 : kk • (kk⁻¹ • p) = p := by
        rw [← hAb.mul_smul, mul_inv_cancel, hAb.one_smul]
      calc (kk⁻¹ * x * kk) • (kk⁻¹ • p)
          = kk⁻¹ • (x • (kk • (kk⁻¹ • p))) := by rw [hAb.mul_smul, hAb.mul_smul]
        _ = kk⁻¹ • (x • p) := by rw [h1]
        _ = kk⁻¹ • p := by rw [hp]
    obtain ⟨jy, my, ey, hhy, Ry, hRyfree, hconjy⟩ :=
      elliptic_normal_form N (hAall N) (hIall N) hAall hIall (kk⁻¹ * x * kk) hy
    obtain ⟨jx, mx, ex, hhx, Rx, hRxfree, hconjx⟩ :=
      elliptic_normal_form N (hAall N) (hIall N) hAall hIall x hx
    have e1 : rotCanon hAall hIall (kk⁻¹ * x * kk) = rotN Ry :=
      rotCanonEqRotN N hAall hIall (kk⁻¹ * x * kk) jy my ey Ry hRyfree hhy hconjy
    have e2 : rotCanon hAall hIall x = rotN Rx :=
      rotCanonEqRotN N hAall hIall x jx mx ex Rx hRxfree hhx hconjx
    rw [e1, e2]
    have hk' : (ey ▸ blk jy my 1 Ry : PO N 1)
        = (hhx⁻¹ * kk * hhy)⁻¹ * (ex ▸ blk jx mx 1 Rx : PO N 1) * (hhx⁻¹ * kk * hhy) := by
      rw [← hconjy, ← hconjx]
      group
    exact (rcRotN_conj_blk ex ey Rx Ry (hhx⁻¹ * kk * hhy) hk').symm
  · have hy : ¬ ∃ p : E N, (kk⁻¹ * x * kk) • p = p := by
      rintro ⟨p, hp⟩
      refine hx ⟨kk • p, ?_⟩
      have h3 : kk * (kk⁻¹ * x * kk) = x * kk := by group
      calc x • (kk • p) = (x * kk) • p := by rw [hAb.mul_smul]
        _ = (kk * (kk⁻¹ * x * kk)) • p := by rw [h3]
        _ = kk • ((kk⁻¹ * x * kk) • p) := by rw [hAb.mul_smul]
        _ = kk • p := by rw [hp]
    rw [rotCanon, dif_neg hy, rotCanon, dif_neg hx]

/-! ## The fixed set of a block element and the separation transfer -/

private lemma gae_fermi_zero_right (k m : ℕ) (v : E k) : fermi k m v 0 = coordEmb k m v := by
  refine nib_eq_of_tanC_nrmC ?_ ?_
  · ext i; simp [tanC, fermi, coordEmb]
  · ext i; simp [nrmC, fermi, coordEmb]

/-- The fixed set of a pure block with fixed-point-free normal part is the standard stratum. -/
lemma gae_fixSet_blk_eq_stdTG (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w, R w = w → w = 0) :
    fixSet (blk j m 1 R) = stdTG j m := by
  ext u
  constructor
  · intro hu
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi j m v w := ⟨_, _, ((fermi_inv j m).2.1 u).symm⟩
    rw [fixSet, Set.mem_setOf_eq] at hu
    rw [blk_smul_fermi j m hAj hIj hA hI 1 R v w, hAj.2.2.2.1 v] at hu
    have h3 := congrArg (fermiInv j m) hu
    rw [(fermi_inv j m).1 v (R w), (fermi_inv j m).1 v w] at h3
    have h2 : R w = w := (Prod.ext_iff.mp h3).2
    have hw : w = 0 := hR w h2
    subst hw
    exact ⟨v, (gae_fermi_zero_right j m v).symm⟩
  · rintro ⟨v, rfl⟩
    rw [fixSet, Set.mem_setOf_eq]
    show (blk j m 1 R) • coordEmb j m v = coordEmb j m v
    rw [← gae_fermi_zero_right j m v, blk_smul_fermi j m hAj hIj hA hI 1 R v 0,
      hAj.2.2.2.1 v, R.map_zero, gae_fermi_zero_right j m v]

/-- An element commuting with `blk j m 1 S` (with `S` fixed-point free) preserves the standard
stratum. -/
lemma gae_mem_setStabStd_of_centralizer {j m : ℕ} (hAj : POActionProp j)
    (hIj : HypIsometryProp j) (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    {S : E m ≃ₗᵢ[ℝ] E m} (hSfree : ∀ w : E m, S w = w → w = 0) {c : PO (j + m) 1}
    (hcomm : blk j m 1 S * c = c * blk j m 1 S) : c ∈ SetStabStd j m := by
  have hP := POBasic.ofProp hA
  have hfix : fixSet (blk j m 1 S) = stdTG j m :=
    gae_fixSet_blk_eq_stdTG j m hAj hIj hA hI S hSfree
  intro u
  rw [← hfix]
  constructor
  · intro hu
    rw [fixSet, Set.mem_setOf_eq] at hu ⊢
    rw [← hP.mul_smul, hcomm, hP.mul_smul, hu]
  · intro hu
    rw [fixSet, Set.mem_setOf_eq] at hu ⊢
    have h2 : c⁻¹ • (blk j m 1 S • (c • u)) = u := by
      rw [hu, ← hP.mul_smul, inv_mul_cancel, hP.one_smul]
    have hconj : c⁻¹ * blk j m 1 S * c = blk j m 1 S := by
      calc c⁻¹ * blk j m 1 S * c = c⁻¹ * (blk j m 1 S * c) := by rw [mul_assoc]
        _ = c⁻¹ * (c * blk j m 1 S) := by rw [hcomm]
        _ = (c⁻¹ * c) * blk j m 1 S := by rw [mul_assoc]
        _ = blk j m 1 S := by rw [inv_mul_cancel, one_mul]
    have h3 : (c⁻¹ * blk j m 1 S * c) • u = u := by
      rw [hP.mul_smul (c⁻¹ * blk j m 1 S) c u, hP.mul_smul c⁻¹ (blk j m 1 S) (c • u)]
      exact h2
    rwa [hconj] at h3

/-- A stratum-stabilising element whose stratum part is trivial fixes the stratum pointwise. -/
lemma gae_smul_eq_self_of_resStd_one {j m : ℕ} (hAj : POActionProp j)
    (hIj : HypIsometryProp j) (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    {c : PO (j + m) 1} (hc : c ∈ SetStabStd j m) (hres : resStd j m c = 1) (v : E j) :
    c • coordEmb j m v = coordEmb j m v := by
  have h1 := stab_eq_blk j m hAj hIj hA hI c hc
  rw [hres] at h1
  rw [h1, rhd_blk_smul_coordEmb j m hAj hIj hA hI (1 : PO j 1) (nrmStd j m c) v,
    hAj.2.2.2.1 v]

/-- If `rotN R < 2` and `R` is fixed-point free then the normal dimension is even. -/
lemma gae_even_of_rotN_lt_two {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m)
    (hR : ∀ w, R w = w → w = 0) (h : rotN R < 2) : Even m := by
  by_contra hnot
  have hodd : Odd m := Nat.not_even_iff_odd.mp hnot
  obtain ⟨ê, hê, hRê⟩ := odd_isometry_neg_eigen R hodd hR
  have h2 : (2 : ℝ) ≤ rotN R := by
    have h1 := nib_apply_le_rotN m R ê
    rw [hê, mul_one] at h1
    have hsub : R ê - ê = (-2 : ℝ) • ê := by rw [hRê]; module
    have hnorm : ‖R ê - ê‖ = 2 := by
      rw [hsub, norm_smul, hê, mul_one, Real.norm_eq_abs]
      norm_num
    linarith [h1, hnorm]
  linarith

/-! ## The engine -/

/-- **The finite-type tube engine for even `n ≥ 4`.** -/
theorem gaeTubeEven (n : ℕ) (hn : 4 ≤ n) (hev : Even n)
    (hA : ∀ k, 2 ≤ k → POActionProp k) (hI : ∀ k, 2 ≤ k → HypIsometryProp k)
    (hCov : ∀ k, 2 ≤ k → k < n → CovolLB k) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (Λ : Subgroup (PO n 1)) (D : Set (E n)) (z : E n),
        IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH n) →
        nearGrp Λ z η ≠ ⊥ → Finite (nearGrp Λ z η) →
        ENNReal.ofReal (c * η ^ (-α)) ≤ volH n D := by
  classical
  have hAall : ∀ k, POActionProp k := rcPOActionProp
  have hIall : ∀ k, HypIsometryProp k := rcHypIsometryProp
  obtain ⟨C₀, hC₀pos, hpiv⟩ := ftbPivotDefs n hAall hIall
  -- a uniform constant: the minimum over all strata `(j, m)` with `j + m = n` and `j ≠ 1`
  let Cst : ℕ × ℕ → ℝ := fun p =>
    if h1 : p.1 + p.2 = n ∧ p.1 ≠ 1 then
      (gaeTube p.1 p.2 (hAall p.1) (hIall p.1) (hAall (p.1 + p.2)) (hIall (p.1 + p.2))
        (fun k h2 hk => hCov k h2 (by rw [h1.1] at hk; exact hk))
        h1.2 (by rw [h1.1]; exact hn) C₀ hC₀pos).choose
    else 1
  have hCst_eq : ∀ p (h1 : p.1 + p.2 = n ∧ p.1 ≠ 1), Cst p =
      (gaeTube p.1 p.2 (hAall p.1) (hIall p.1) (hAall (p.1 + p.2)) (hIall (p.1 + p.2))
        (fun k h2 hk => hCov k h2 (by rw [h1.1] at hk; exact hk))
        h1.2 (by rw [h1.1]; exact hn) C₀ hC₀pos).choose := by
    intro p h1
    exact dif_pos h1
  have hCst_pos : ∀ p, 0 < Cst p := by
    intro p
    by_cases h1 : p.1 + p.2 = n ∧ p.1 ≠ 1
    · rw [hCst_eq p h1]
      exact (gaeTube p.1 p.2 (hAall p.1) (hIall p.1) (hAall (p.1 + p.2)) (hIall (p.1 + p.2))
        (fun k h2 hk => hCov k h2 (by rw [h1.1] at hk; exact hk))
        h1.2 (by rw [h1.1]; exact hn) C₀ hC₀pos).choose_spec.1
    · rw [show Cst p = 1 from dif_neg h1]
      norm_num
  let P2 : Finset (ℕ × ℕ) := (Finset.range (n + 1)).product (Finset.range (n + 1))
  let vals : Finset ℝ := P2.image Cst
  have hvals_ne : vals.Nonempty :=
    ⟨Cst (0, 0), Finset.mem_image.mpr ⟨(0, 0),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      rfl⟩⟩
  let cst : ℝ := vals.min' hvals_ne
  have hcst_pos : 0 < cst := by
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (Finset.min'_mem vals hvals_ne)
    have hp' : Cst p = cst := hp
    rw [← hp']
    exact hCst_pos p
  have hcst_le : ∀ p, p ∈ P2 → cst ≤ Cst p := fun p hp =>
    Finset.min'_le vals (Cst p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  refine ⟨cst, 1, hcst_pos, one_pos, min 1 (1 / C₀),
    lt_min one_pos (one_div_pos.mpr hC₀pos), ?hmain⟩
  intro η hη0 hηη0 Λ D z hdisc hD hnear hfin
  have hη1 : η ≤ 1 := le_trans hηη0 (min_le_left 1 _)
  have hηK : η ≤ 1 / C₀ := le_trans hηη0 (min_le_right 1 _)
  have hKη1 : C₀ * η ≤ 1 := by
    calc C₀ * η ≤ C₀ * (1 / C₀) := mul_le_mul_of_nonneg_left hηK (le_of_lt hC₀pos)
      _ = 1 := by field_simp
  obtain ⟨g, hgΛ, hgne, hgnear⟩ := exists_nearId_of_nearGrp_ne_bot hnear
  have hgmem : g ∈ nearGrp Λ z η := Subgroup.subset_closure ⟨hgΛ, hgnear⟩
  obtain ⟨y, hy⟩ := finiteFixes n (hAall n) (nearGrp Λ z η) hfin
  obtain ⟨b, hbΛ, hbne, hbfix, hbrot, hbsep⟩ :=
    hpiv Λ z η g hdisc hgΛ hgne hη0 hη1 hgnear ⟨y, hy g hgmem⟩
  obtain ⟨j, m, e, hh, R, hRfree, hconj⟩ :=
    elliptic_normal_form n (hAall n) (hIall n) hAall hIall b hbfix
  have hrot_eq : rotCanon hAall hIall b = rotN R :=
    rotCanonEqRotN n hAall hIall b j m e R hRfree hh hconj
  have hrot_le : rotN R ≤ C₀ * η := by rw [← hrot_eq]; exact hbrot
  have hrot_lt : rotN R < 2 := lt_of_le_of_lt (le_trans hrot_le hKη1) (by norm_num)
  have hm_even : Even m := gae_even_of_rotN_lt_two R hRfree hrot_lt
  have hj_even : Even j := by
    have h1 : Even (j + m) := e.symm ▸ hev
    exact (Nat.even_add.mp h1).mpr hm_even
  have hj1 : j ≠ 1 := by
    intro hj
    rw [hj] at hj_even
    obtain ⟨r, hr⟩ := hj_even
    omega
  subst e
  have hconj' : hh⁻¹ * b * hh = blk j m 1 R := hconj
  have hb_eq : b = hh * (blk j m 1 R) * hh⁻¹ := by
    rw [← hconj']
    group
  have hRne : R ≠ 1 := by
    intro hR1
    apply hbne
    rw [hb_eq, hR1, (blk_hom j m (hAall j) (hIall j) (hAall (j + m)) (hIall (j + m))).2.1,
      mul_one, mul_inv_cancel]
  have hrot_pos : 0 < rotN R := gae_rotN_pos_of_ne_one R hRne
  -- the conjugated configuration
  set Λ₁ : Subgroup (PO (j + m) 1) := Λ.map (MulAut.conj hh⁻¹).toMonoidHom with hΛ₁
  set D₁ : Set (E (j + m)) := (fun u : E (j + m) => hh⁻¹ • u) '' D with hD₁
  have hb₁ : blk j m 1 R ∈ Λ₁ := by
    rw [hΛ₁]
    refine Subgroup.mem_map.mpr ⟨b, hbΛ, ?_⟩
    show (MulAut.conj hh⁻¹) b = blk j m 1 R
    rw [MulAut.conj_apply, inv_inv]
    exact hconj'
  have hdisc₁ : IsDiscrete (SetLike.coe Λ₁) := by
    rw [hΛ₁]
    have hφ : Topology.IsInducing (fun x : PO (j + m) 1 => hh⁻¹ * x * hh) := by
      have h1 : (fun x : PO (j + m) 1 => hh⁻¹ * x * hh)
          = ⇑((Homeomorph.mulLeft hh⁻¹).trans (Homeomorph.mulRight hh)) := rfl
      rw [h1]
      exact Homeomorph.isInducing _
    have hfun : (⇑(MulAut.conj hh⁻¹).toMonoidHom : PO (j + m) 1 → PO (j + m) 1)
        = fun x => hh⁻¹ * x * hh := by
      funext y
      show (MulAut.conj hh⁻¹) y = hh⁻¹ * y * hh
      rw [MulAut.conj_apply, inv_inv]
    have himg : (SetLike.coe (Λ.map (MulAut.conj hh⁻¹).toMonoidHom) : Set (PO (j + m) 1))
        = (fun x : PO (j + m) 1 => hh⁻¹ * x * hh) '' (SetLike.coe Λ) := by
      rw [Subgroup.coe_map, hfun]
    rw [himg]
    exact hdisc.image hφ
  have hD₁fd : IsFundamentalDomain Λ₁ D₁ (volH (j + m)) := by
    rw [hΛ₁, hD₁]
    exact conj_fundamentalDomain (j + m) (hAall (j + m)) (hIall (j + m)) Λ D hD hh⁻¹
  have hvol₁ : volH (j + m) D₁ = volH (j + m) D := by
    rw [hD₁]
    have hmp := (HypIsoData.ofProp (hIall (j + m))).measurePreserving_smul hh⁻¹
    have hinj : Function.Injective (fun u : E (j + m) => hh⁻¹ • u) := by
      intro a b hab
      have hAb := POBasic.ofProp (hAall (j + m))
      have h4 := congrArg (fun u => hh • u) hab
      rwa [← hAb.mul_smul, ← hAb.mul_smul, mul_inv_cancel, hAb.one_smul, hAb.one_smul] at h4
    rw [← hmp.measure_preimage hD₁fd.nullMeasurableSet, Set.preimage_image_eq D hinj]
  -- the separation for the tube, transported from the pivot's separation
  have hfixblk : fixSet (blk j m 1 R) = stdTG j m :=
    gae_fixSet_blk_eq_stdTG j m (hAall j) (hIall j) (hAall (j + m)) (hIall (j + m)) R hRfree
  have hsep : ∀ c : PO (j + m) 1, c ∈ Λ₁ →
      c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
      resStd j m c = 1 → c ≠ 1 → rotN R ≤ C₀ * rotN (nrmStd j m c) := by
    intro c hcΛ₁ hcC hcres hcne
    have hAn := POBasic.ofProp (hAall (j + m))
    have hcomm : blk j m 1 R * c = c * blk j m 1 R :=
      hcC (blk j m 1 R) (Set.mem_singleton _)
    have hcstab : c ∈ SetStabStd j m :=
      gae_mem_setStabStd_of_centralizer (hAall j) (hIall j) (hAall (j + m)) (hIall (j + m))
        hRfree hcomm
    have hcfix : ∀ v : E j, c • coordEmb j m v = coordEmb j m v := fun v =>
      gae_smul_eq_self_of_resStd_one (hAall j) (hIall j) (hAall (j + m)) (hIall (j + m))
        hcstab hcres v
    -- transport to the original lattice
    obtain ⟨c₀, hc₀Λ, hc₀eq⟩ := Subgroup.mem_map.mp (by rw [← hΛ₁]; exact hcΛ₁)
    have hc₀c : c₀ = hh * c * hh⁻¹ := by
      have h2 : hh⁻¹ * c₀ * hh = c := by
        have h3 : (MulAut.conj hh⁻¹) c₀ = c := hc₀eq
        rwa [MulAut.conj_apply, inv_inv] at h3
      rw [← h2]
      group
    have hc₀ne : c₀ ≠ 1 := by
      intro h1
      apply hcne
      have hcmap : (MulAut.conj hh⁻¹).toMonoidHom c₀ = 1 := by rw [h1, map_one]
      rw [← hc₀eq, hcmap]
    have hbcomm : c₀ ∈ Subgroup.centralizer ({b} : Set (PO (j + m) 1)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [hc₀c, hb_eq]
      calc (hh * (blk j m 1 R) * hh⁻¹) * (hh * c * hh⁻¹)
          = hh * ((blk j m 1 R) * c) * hh⁻¹ := by group
        _ = hh * (c * (blk j m 1 R)) * hh⁻¹ := by rw [hcomm]
        _ = (hh * c * hh⁻¹) * (hh * (blk j m 1 R) * hh⁻¹) := by group
    have hc₀fix : ∀ u : E (j + m), b • u = u → c₀ • u = u := by
      intro u hu
      have h2 : (hh * (blk j m 1 R) * hh⁻¹) • u = u := by rw [← hb_eq]; exact hu
      have h6 : hh • (blk j m 1 R • (hh⁻¹ • u)) = u := by
        rwa [hAn.mul_smul, hAn.mul_smul] at h2
      have h7 := congrArg (fun v => hh⁻¹ • v) h6
      have h8 : (hh⁻¹ * hh) • (blk j m 1 R • (hh⁻¹ • u)) = hh⁻¹ • u := by
        rwa [← hAn.mul_smul] at h7
      have h9 : blk j m 1 R • (hh⁻¹ • u) = hh⁻¹ • u := by
        simpa [inv_mul_cancel, hAn.one_smul] using h8
      have hw : hh⁻¹ • u ∈ stdTG j m := by
        rw [← hfixblk]
        exact h9
      obtain ⟨v, hv⟩ := hw
      have h3 : c • (hh⁻¹ • u) = hh⁻¹ • u := by
        rw [← hv]
        exact hcfix v
      calc c₀ • u = (hh * c * hh⁻¹) • u := by rw [hc₀c]
        _ = hh • (c • (hh⁻¹ • u)) := by rw [hAn.mul_smul, hAn.mul_smul]
        _ = hh • (hh⁻¹ • u) := by rw [h3]
        _ = u := by
              have h10 : (hh * hh⁻¹) • u = u := by rw [mul_inv_cancel, hAn.one_smul]
              rwa [hAn.mul_smul] at h10
    have hbt := hbsep c₀ hc₀Λ hbcomm hc₀fix hc₀ne
    have e1 : rotCanon hAall hIall c₀ = rotCanon hAall hIall c := by
      have h := gaeRotCanonConj hAall hIall c hh⁻¹
      simp only [inv_inv] at h
      rw [hc₀c]
      exact h
    obtain ⟨hc_eq, _⟩ := geeBlkFixStd j m c hcfix
    have e2 : rotCanon hAall hIall c = rotN (nrmStd j m c) := by
      conv_lhs => rw [hc_eq]
      exact gaeRotCanonBlk hAall hIall (rfl : j + m = j + m) (nrmStd j m c)
    calc rotN R = rotCanon hAall hIall b := hrot_eq.symm
      _ ≤ C₀ * rotCanon hAall hIall c₀ := hbt
      _ = C₀ * rotCanon hAall hIall c := by rw [e1]
      _ = C₀ * rotN (nrmStd j m c) := by rw [e2]
  -- the tube inequality at the stratum `(j, m)`, with the constant `Cst (j, m)`
  have hmem2 : (j, m) ∈ P2 :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have h1 : (j, m).1 + (j, m).2 = j + m ∧ (j, m).1 ≠ 1 := ⟨rfl, hj1⟩
  have hcle : cst ≤ Cst (j, m) := hcst_le (j, m) hmem2
  rw [hCst_eq (j, m) h1] at hcle
  have htube := (gaeTube (j, m).1 (j, m).2 (hAall (j, m).1) (hIall (j, m).1)
      (hAall ((j, m).1 + (j, m).2)) (hIall ((j, m).1 + (j, m).2))
      (fun k h2 hk => hCov k h2 (by rw [h1.1] at hk; exact hk))
      h1.2 (by rw [h1.1]; exact hn) C₀ hC₀pos).choose_spec.2
    Λ₁ D₁ 0 η R hdisc₁ hD₁fd hη0 hη1 hb₁ hRfree hrot_pos hrot_le hsep
  rw [hvol₁] at htube
  exact le_trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hcle (Real.rpow_nonneg (le_of_lt hη0) _))) htube

end Work.Mostow
