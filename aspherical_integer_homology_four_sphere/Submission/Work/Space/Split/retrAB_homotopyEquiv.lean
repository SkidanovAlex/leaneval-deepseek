import Mathlib
import Submission.Work.Space.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! **`A ∩ B` deformation retracts onto the glued boundary `⊔_v ∂[-1,1]² × T_v`.**

We prove that the open set `A ∩ B ⊆ M̂` is homotopy equivalent to the boundary
`⊔_v ∂[-1,1]² × T_v` of the filling pieces.  The proof goes through the "annulus"
`{1/4 < ‖p‖∞ < 1}` inside the filling pieces:

* `A ∩ B = incY '' {q | 1/4 < sqNorm q.2.1 ∧ sqNorm q.2.1 < 1}` (`incY` being injective
  and an open embedding on `{sqNorm < 1}`), so `A ∩ B` is homeomorphic to the "sigma"
  space `Σ v, {p // 1/4 < sqNorm p ∧ sqNorm p < 1} × T_v`;
* that sigma space is homotopy equivalent to `Σ v, {p // sqNorm p = 1} × T_v` by the
  radial scaling `p ↦ (sqNorm p)⁻¹ • p` with homotopy inverse `p ↦ (1/2) • p` and the
  straight-line homotopy `p ↦ ((s + (1-s)/(2 sqNorm p))) • p`, which keeps the layer in
  the annulus `(1/4, 1)`.
-/

noncomputable section

open Set Topology Function
open scoped Topology

namespace Work.Space.Split

/-! ## Elementary facts about the sup norm on the square -/

theorem nrm_smul (c : ℝ) (p : E2) : nrm (c • p) = |c| * nrm p := by
  rw [nrm, nrm]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [abs_mul, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg c)]

theorem mem_Sq_of_nrm_le_one {q : E2} (h : nrm q ≤ 1) : q ∈ Sq :=
  ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩

theorem sqNorm_le_one (p : SquarePt) : sqNorm p ≤ 1 := max_le p.2.1 p.2.2

theorem inv_mul_sqNorm_le_one (p : SquarePt) : (sqNorm p)⁻¹ * sqNorm p ≤ 1 := by
  rcases eq_or_ne (sqNorm p) 0 with h | h
  · rw [h, inv_zero, zero_mul]; norm_num
  · rw [inv_mul_cancel₀ h]

theorem sqNorm_inv_smul_Sq (p : SquarePt) : (sqNorm p)⁻¹ • (p : E2) ∈ Sq := by
  refine mem_Sq_of_nrm_le_one ?_
  rw [nrm_smul]
  change |(sqNorm p)⁻¹| * sqNorm p ≤ 1
  rw [abs_of_nonneg (inv_nonneg.mpr (sqNorm_nonneg p))]
  exact inv_mul_sqNorm_le_one p

/-- The "halving" map `p ↦ (1/2) • p` on the square. -/
noncomputable def halfPt (p : SquarePt) : SquarePt :=
  ⟨(1/2 : ℝ) • (p : E2), by
    refine mem_Sq_of_nrm_le_one ?_
    rw [nrm_smul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    change (1/2) * sqNorm p ≤ 1
    linarith [sqNorm_nonneg p, sqNorm_le_one p]⟩

theorem halfPt_sqNorm (p : SquarePt) : sqNorm (halfPt p) = 1/2 * sqNorm p := by
  show nrm ((1/2 : ℝ) • (p : E2)) = 1/2 * sqNorm p
  rw [nrm_smul]
  change |(1/2:ℝ)| * sqNorm p = 1/2 * sqNorm p
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]

theorem continuous_halfPt : Continuous halfPt := by
  unfold halfPt
  refine Continuous.subtype_mk ?_ _
  exact (continuous_const : Continuous (fun _ : SquarePt => (1/2:ℝ))).smul continuous_subtype_val

/-! ## The two subtypes of the square and the radial map -/

/-- The points of the annulus layer of the square: `1/4 < ‖p‖∞ < 1`. -/
abbrev AnnPt : Type := {p : SquarePt // 1/4 < sqNorm p ∧ sqNorm p < 1}

/-- The boundary points of the square: `‖p‖∞ = 1`. -/
abbrev BdryPt : Type := {p : SquarePt // sqNorm p = 1}

/-- The radial map `p ↦ (sqNorm p)⁻¹ • p`, sending the annulus `AnnPt` onto the boundary
`BdryPt`. -/
noncomputable def dirPt (p : AnnPt) : BdryPt :=
  ⟨⟨(sqNorm p.1)⁻¹ • (p.1 : E2), sqNorm_inv_smul_Sq p.1⟩, by
    have hne : sqNorm p.1 ≠ 0 := ne_of_gt (lt_trans (by norm_num) p.2.1)
    show nrm ((sqNorm p.1)⁻¹ • (p.1 : E2)) = 1
    rw [nrm_smul]
    change |(sqNorm p.1)⁻¹| * sqNorm p.1 = 1
    rw [abs_of_nonneg (inv_nonneg.mpr (sqNorm_nonneg p.1)), inv_mul_cancel₀ hne]⟩

theorem continuous_dirPt : Continuous dirPt := by
  refine Continuous.subtype_mk ?_ _
  refine Continuous.subtype_mk ?_ _
  have hne : ∀ p : AnnPt, sqNorm p.1 ≠ 0 := fun p => ne_of_gt (lt_trans (by norm_num) p.2.1)
  have hinv : Continuous fun p : AnnPt => (sqNorm p.1)⁻¹ :=
    (continuous_sqNorm.comp continuous_subtype_val).inv₀ hne
  exact hinv.smul (continuous_subtype_val.comp continuous_subtype_val)

/-- The halving map `p ↦ (1/2) • p`, sending the boundary `BdryPt` into the annulus
`AnnPt`. -/
noncomputable def halfPtAnn (q : BdryPt) : AnnPt :=
  ⟨halfPt q.1, by rw [halfPt_sqNorm, q.2]; norm_num⟩

theorem continuous_halfPtAnn : Continuous halfPtAnn := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_halfPt.comp continuous_subtype_val

theorem dirPt_halfPtAnn (q : BdryPt) : dirPt (halfPtAnn q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  show (sqNorm (halfPt q.1))⁻¹ • ((halfPt q.1 : SquarePt) : E2) = (q.1 : E2)
  rw [halfPt_sqNorm, q.2]
  simp only [mul_one]
  rw [show ((halfPt q.1 : SquarePt) : E2) = (1/2 : ℝ) • (q.1 : E2) from rfl, smul_smul]
  norm_num

/-! ## The straight-line homotopy scalar -/

/-- The scalar `s + (1-s)/(2‖p‖∞)` multiplying the square coordinate during the
straight-line homotopy. -/
def cHom (sp : unitInterval × AnnPt) : ℝ :=
  (sp.1 : ℝ) + (1 - (sp.1 : ℝ)) * (2 * sqNorm sp.2.1)⁻¹

/-- The layer parameter of the point `cHom sp • p` of the straight-line homotopy:
`s·‖p‖∞ + (1-s)/2`. -/
def valHom (sp : unitInterval × AnnPt) : ℝ :=
  (sp.1 : ℝ) * sqNorm sp.2.1 + (1 - (sp.1 : ℝ)) * (1/2)

theorem half_le_inv_two_mul (sp : unitInterval × AnnPt) :
    (1:ℝ)/2 ≤ (2 * sqNorm sp.2.1)⁻¹ := by
  have hβ0 : 0 < sqNorm sp.2.1 := lt_trans (by norm_num) sp.2.2.1
  have hβ1 : sqNorm sp.2.1 ≤ 1 := le_of_lt sp.2.2.2
  have := one_div_le_one_div_of_le (show (0:ℝ) < 2 * sqNorm sp.2.1 by positivity)
    (show 2 * sqNorm sp.2.1 ≤ 2 by linarith)
  simpa [one_div] using this

theorem cHom_ge_half (sp : unitInterval × AnnPt) : 1/2 ≤ cHom sp := by
  have h := half_le_inv_two_mul sp
  have hs0 : 0 ≤ (sp.1 : ℝ) := sp.1.2.1
  have hs1 : (sp.1 : ℝ) ≤ 1 := sp.1.2.2
  have hmul : 0 ≤ 1 - (sp.1 : ℝ) := by linarith
  have h2 := mul_le_mul_of_nonneg_left h hmul
  unfold cHom
  linarith

theorem cHom_pos (sp : unitInterval × AnnPt) : 0 < cHom sp :=
  lt_of_lt_of_le (by norm_num) (cHom_ge_half sp)

theorem cHom_mul_sqNorm (sp : unitInterval × AnnPt) :
    cHom sp * sqNorm sp.2.1 = valHom sp := by
  have hβ0 : 0 < sqNorm sp.2.1 := lt_trans (by norm_num) sp.2.2.1
  have h2 : (2 * sqNorm sp.2.1)⁻¹ * (2 * sqNorm sp.2.1) = 1 :=
    inv_mul_cancel₀ (ne_of_gt (by linarith))
  have h : (2 * sqNorm sp.2.1)⁻¹ * sqNorm sp.2.1 = 1/2 := by nlinarith [h2]
  unfold cHom valHom
  rw [add_mul, mul_assoc, h]

theorem valHom_gt (sp : unitInterval × AnnPt) : 1/4 < valHom sp := by
  have hβ : (1/4:ℝ) < sqNorm sp.2.1 := sp.2.2.1
  have hs0 : 0 ≤ (sp.1 : ℝ) := sp.1.2.1
  have hs1 : (sp.1 : ℝ) ≤ 1 := sp.1.2.2
  unfold valHom
  rcases eq_or_lt_of_le hs1 with h | h
  · rw [h]; ring_nf; linarith
  · nlinarith [mul_pos (sub_pos.mpr h) (by norm_num : (0:ℝ) < 1/4),
      mul_nonneg hs0 (sub_nonneg.mpr (le_of_lt hβ))]

theorem valHom_lt (sp : unitInterval × AnnPt) : valHom sp < 1 := by
  have hβ : sqNorm sp.2.1 < 1 := sp.2.2.2
  have hs0 : 0 ≤ (sp.1 : ℝ) := sp.1.2.1
  have hs1 : (sp.1 : ℝ) ≤ 1 := sp.1.2.2
  unfold valHom
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; ring_nf; norm_num
  · nlinarith [mul_pos h (sub_pos.mpr hβ), mul_nonneg (sub_nonneg.mpr hs1) (by norm_num : (0:ℝ) ≤ 1/2)]

/-- The square point `cHom sp • p` of the straight-line homotopy. -/
def scalePtSq (sp : unitInterval × AnnPt) : SquarePt :=
  ⟨cHom sp • (sp.2.1 : E2), by
    refine mem_Sq_of_nrm_le_one ?_
    rw [nrm_smul]
    change |cHom sp| * sqNorm sp.2.1 ≤ 1
    rw [abs_of_nonneg (le_of_lt (cHom_pos sp)), cHom_mul_sqNorm sp]
    exact le_of_lt (valHom_lt sp)⟩

theorem sqNorm_scalePtSq (sp : unitInterval × AnnPt) : sqNorm (scalePtSq sp) = valHom sp := by
  show nrm (cHom sp • (sp.2.1 : E2)) = valHom sp
  rw [nrm_smul]
  change |cHom sp| * sqNorm sp.2.1 = valHom sp
  rw [abs_of_nonneg (le_of_lt (cHom_pos sp)), cHom_mul_sqNorm sp]

/-- The point of the annulus layer at parameter `sp` of the straight-line homotopy. -/
def scalePtAnn (sp : unitInterval × AnnPt) : AnnPt :=
  ⟨scalePtSq sp, by rw [sqNorm_scalePtSq]; exact ⟨valHom_gt sp, valHom_lt sp⟩⟩

theorem continuous_scalePtSq : Continuous scalePtSq := by
  unfold scalePtSq
  refine Continuous.subtype_mk ?_ _
  have hβ : Continuous fun sp : unitInterval × AnnPt => sqNorm sp.2.1 :=
    continuous_sqNorm.comp (continuous_subtype_val.comp continuous_snd)
  have hc : Continuous fun sp : unitInterval × AnnPt => cHom sp := by
    unfold cHom
    refine Continuous.add (continuous_subtype_val.comp continuous_fst) ?_
    refine Continuous.mul (Continuous.sub continuous_const (continuous_subtype_val.comp continuous_fst)) ?_
    exact (Continuous.mul continuous_const hβ).inv₀ (fun sp =>
      ne_of_gt (mul_pos (by norm_num) (lt_trans (by norm_num) sp.2.2.1)))
  exact hc.smul (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))

theorem continuous_scalePtAnn : Continuous scalePtAnn := by
  unfold scalePtAnn
  exact Continuous.subtype_mk continuous_scalePtSq _

theorem scalePt_zeroAnn (p : AnnPt) : scalePtAnn (0, p) = halfPtAnn (dirPt p) := by
  apply Subtype.ext
  apply Subtype.ext
  show cHom (0, p) • (p.1 : E2) = (1/2 : ℝ) • ((sqNorm p.1)⁻¹ • (p.1 : E2))
  have h : cHom (0, p) = (1/2 : ℝ) * (sqNorm p.1)⁻¹ := by
    show (0 : ℝ) + (1 - 0) * (2 * sqNorm p.1)⁻¹ = (1/2 : ℝ) * (sqNorm p.1)⁻¹
    rw [zero_add, sub_zero, one_mul, mul_inv_rev]
    ring
  rw [h, smul_smul]

theorem scalePt_oneAnn (p : AnnPt) : scalePtAnn (1, p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  show cHom (1, p) • (p.1 : E2) = (p.1 : E2)
  have h : cHom (1, p) = 1 := by
    show (1 : ℝ) + (1 - 1) * (2 * sqNorm p.1)⁻¹ = 1
    rw [sub_self, zero_mul, add_zero]
  rw [h, one_smul]


/-! ## Generic homeomorphisms for `Sigma` and `Prod` subtypes -/

/-- A subtype of a product defined only by a condition on the first factor is the product of
the corresponding subtype with the second factor. -/
noncomputable def subtypeProdHomeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (p : α → Prop) : {s : α × β // p s.1} ≃ₜ {a // p a} × β where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun x := ⟨(x.1.1, x.2), x.1.2⟩
  left_inv x := by rcases x with ⟨⟨a, b⟩, h⟩; rfl
  right_inv x := by rcases x with ⟨⟨a, h⟩, b⟩; rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact Continuous.prodMk (Continuous.comp continuous_subtype_val continuous_fst) continuous_snd

/-- A family of homeomorphisms induces a homeomorphism of the `Sigma` types. -/
noncomputable def sigmaCongrRightHomeomorph {ι : Type*} {X Y : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] (F : ∀ i, X i ≃ₜ Y i) :
    (Σ i, X i) ≃ₜ (Σ i, Y i) where
  toEquiv := Equiv.sigmaCongrRight (fun i => (F i).toEquiv)
  continuous_toFun := Continuous.sigma_map (fun i => (F i).continuous)
  continuous_invFun := Continuous.sigma_map (fun i => (F i).symm.continuous)

/-- A subtype of a `Sigma` type defined componentwise is the `Sigma` of the subtypes. -/
noncomputable def subtypeSigmaHomeomorph {ι : Type*} {β : ι → Type*}
    [∀ i, TopologicalSpace (β i)] (P : (i : ι) → β i → Prop) :
    {x : (Σ i, β i) // P x.1 x.2} ≃ₜ (Σ i, {b : β i // P i b}) := by
  have hemb : IsEmbedding (Sigma.map id (fun i => (Subtype.val : {b : β i // P i b} → β i))) := by
    rw [isEmbedding_sigmaMap Function.injective_id]
    intro i; exact IsEmbedding.subtypeVal
  have hrange : range (Sigma.map id (fun i => (Subtype.val : {b : β i // P i b} → β i)))
      = {x : (Σ i, β i) | P x.1 x.2} := by
    ext x
    constructor
    · rintro ⟨⟨i, b⟩, rfl⟩; exact b.2
    · intro hx; exact ⟨⟨x.1, ⟨x.2, hx⟩⟩, rfl⟩
  exact (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm

/-! ## The annular and boundary sigma spaces of the filling -/

/-- The annulus layer of the filling pieces: `Σ_v {p // 1/4 < ‖p‖∞ < 1} × T_v`. -/
abbrev AnnSig (a : Assembly) : Type _ := Σ v : Cusp, AnnPt × a.Torus v

/-- The glued boundary of the filling pieces: `Σ_v ∂[-1,1]² × T_v`. -/
abbrev BdrySig (a : Assembly) : Type _ := Σ v : Cusp, BdryPt × a.Torus v

/-- Radial scaling, on the sigma space. -/
def annToBdry (a : Assembly) : AnnSig a → BdrySig a :=
  Sigma.map id (fun _ => Prod.map dirPt id)

/-- Halving, on the sigma space. -/
def bdryToAnn (a : Assembly) : BdrySig a → AnnSig a :=
  Sigma.map id (fun _ => Prod.map halfPtAnn id)

theorem continuous_annToBdry (a : Assembly) : Continuous (annToBdry a) :=
  Continuous.sigma_map fun _ =>
    Continuous.prodMk (continuous_dirPt.comp continuous_fst) continuous_snd

theorem continuous_bdryToAnn (a : Assembly) : Continuous (bdryToAnn a) :=
  Continuous.sigma_map fun _ =>
    Continuous.prodMk (continuous_halfPtAnn.comp continuous_fst) continuous_snd

theorem annToBdry_bdryToAnn (a : Assembly) (y : BdrySig a) :
    annToBdry a (bdryToAnn a y) = y := by
  obtain ⟨v, q, t⟩ := y
  show (⟨v, (dirPt (halfPtAnn q), t)⟩ : BdrySig a) = ⟨v, (q, t)⟩
  rw [dirPt_halfPtAnn]

/-! ## The straight-line homotopy on the sigma space -/

/-- The straight-line homotopy on the fibers, distributed over the parameters. -/
def gHom (a : Assembly) (v : Cusp) :
    (AnnPt × a.Torus v) × unitInterval → AnnPt × a.Torus v :=
  fun w => (scalePtAnn (w.2, w.1.1), w.1.2)

theorem continuous_gHom (a : Assembly) (v : Cusp) : Continuous (gHom a v) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_scalePtAnn.comp
      (Continuous.prodMk continuous_snd (continuous_fst.comp continuous_fst))
  · exact continuous_snd.comp continuous_fst

/-- The straight-line homotopy on the sigma space. -/
def homSigmaMap (a : Assembly) :
    (Σ v : Cusp, (AnnPt × a.Torus v) × unitInterval) → AnnSig a :=
  Sigma.map id (fun v => gHom a v)

theorem continuous_homSigmaMap (a : Assembly) : Continuous (homSigmaMap a) :=
  Continuous.sigma_map (continuous_gHom a)

/-- Distribution of the parameter of the homotopy. -/
noncomputable def eHom (a : Assembly) :
    unitInterval × AnnSig a ≃ₜ (Σ v : Cusp, (AnnPt × a.Torus v) × unitInterval) :=
  (Homeomorph.prodComm unitInterval (AnnSig a)).trans Homeomorph.sigmaProdDistrib

/-- The underlying map of the straight-line homotopy. -/
def Hmap (a : Assembly) : unitInterval × AnnSig a → AnnSig a :=
  fun x => homSigmaMap a (eHom a x)

theorem continuous_Hmap (a : Assembly) : Continuous (Hmap a) :=
  (continuous_homSigmaMap a).comp (eHom a).continuous

theorem Hmap_apply (a : Assembly) (s : unitInterval) (v : Cusp) (p : AnnPt) (t : a.Torus v) :
    Hmap a (s, (⟨v, (p, t)⟩ : AnnSig a)) = (⟨v, (scalePtAnn (s, p), t)⟩ : AnnSig a) := rfl

theorem Hmap_zero (a : Assembly) (x : AnnSig a) : Hmap a (0, x) = bdryToAnn a (annToBdry a x) := by
  obtain ⟨v, p, t⟩ := x
  rw [Hmap_apply a 0 v p t]
  show (⟨v, (scalePtAnn (0, p), t)⟩ : AnnSig a)
      = (⟨v, (halfPtAnn (dirPt p), t)⟩ : AnnSig a)
  rw [scalePt_zeroAnn]

theorem Hmap_one (a : Assembly) (x : AnnSig a) :
    Hmap a (1, x) = ContinuousMap.id (AnnSig a) x := by
  obtain ⟨v, p, t⟩ := x
  rw [Hmap_apply a 1 v p t]
  show (⟨v, (scalePtAnn (1, p), t)⟩ : AnnSig a) = (⟨v, (p, t)⟩ : AnnSig a)
  rw [scalePt_oneAnn]

/-! ## The homotopy equivalence -/

/-- Radial scaling `Σ_v {p // 1/4 < ‖p‖∞ < 1} × T_v ≃ₕ Σ_v ∂[-1,1]² × T_v`. -/
noncomputable def heAnnBdry (a : Assembly) :
    ContinuousMap.HomotopyEquiv (AnnSig a) (BdrySig a) :=
  ContinuousMap.HomotopyEquiv.mk
    ⟨annToBdry a, continuous_annToBdry a⟩
    ⟨bdryToAnn a, continuous_bdryToAnn a⟩
    ⟨ContinuousMap.Homotopy.mk ⟨Hmap a, continuous_Hmap a⟩ (Hmap_zero a) (Hmap_one a)⟩
    (by
      have h : (⟨annToBdry a, continuous_annToBdry a⟩ :
          C(AnnSig a, BdrySig a)).comp ⟨bdryToAnn a, continuous_bdryToAnn a⟩
          = ContinuousMap.id (BdrySig a) :=
        ContinuousMap.ext (fun y => annToBdry_bdryToAnn a y)
      rw [h])


/-! ## `A ∩ B` as the open annulus, and its identification with the annulus sigma space -/

/-- The open annulus `{1/4 < ‖p‖∞ < 1}` of the filling pieces, as a subspace of `M̂`. -/
abbrev AnnX (a : Assembly) : Type _ := {q : a.Y // q ∈ annulus a.Torus}

/-- The source `A ∩ B` of the homotopy equivalence. -/
abbrev Src (a : Assembly) : Type _ := {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}

/-- **`incY` is an open embedding on the inner core.** -/
theorem isOpen_incY_image (a : Assembly) {U : Set a.Y} (hU : IsOpen U)
    (hUsub : U ⊆ innerCore a.Torus) : IsOpen (a.incY '' U) := by
  rw [a.isOpen_iff_sum]
  refine ⟨?_, ?_⟩
  · have h : {x : a.Mbar | a.incMbar x ∈ a.incY '' U} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, mem_image]
      rintro ⟨q, hq, hxq⟩
      obtain ⟨hx, hgl⟩ := a.incMbar_eq_incY_iff.mp hxq.symm
      have hq1 : sqNorm q.2.1 = 1 := by
        have hg := (a.glue ⟨x, hx⟩).2
        rw [hgl] at hg
        exact hg
      have hq2 : sqNorm q.2.1 < 1 := hUsub hq
      linarith
    rw [h]; exact isOpen_empty
  · have h : {y : a.Y | a.incY y ∈ a.incY '' U} = U := by
      ext y
      simp only [mem_ofPred_eq]
      exact ⟨fun ⟨q, hq, hyq⟩ => by rwa [a.incY_injective hyq] at hq, fun hy => ⟨y, hy, rfl⟩⟩
    rw [h]; exact hU

/-- The identification of the annulus in `M̂` with the annulus in the filling pieces. -/
def phiAnnSrc (a : Assembly) : AnnX a → Src a :=
  fun q => ⟨a.incY q.1, a.incY_mem_Aset_iff.mpr q.2.1, a.incY_mem_Bset_iff.mpr q.2.2⟩

theorem continuous_phiAnnSrc (a : Assembly) : Continuous (phiAnnSrc a) :=
  Continuous.subtype_mk (a.continuous_incY.comp continuous_subtype_val) _

theorem phiAnnSrc_bijective (a : Assembly) : Function.Bijective (phiAnnSrc a) := by
  constructor
  · rintro q q' h
    apply Subtype.ext
    exact a.incY_injective (congrArg Subtype.val h)
  · rintro ⟨z, hz⟩
    have hB : z ∈ a.incY '' innerCore a.Torus := hz.2
    obtain ⟨q, hq, hqeq⟩ := hB
    have hA : a.incY q ∈ a.Aset := by rw [hqeq]; exact hz.1
    have hout : q ∈ outerShell a.Torus := a.incY_mem_Aset_iff.mp hA
    refine ⟨⟨q, ⟨hout, hq⟩⟩, ?_⟩
    apply Subtype.ext
    exact hqeq

theorem isOpenMap_phiAnnSrc (a : Assembly) : IsOpenMap (phiAnnSrc a) := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hU' : IsOpen (Subtype.val '' U : Set a.Y) := by
    have hEq : (Subtype.val '' U : Set a.Y) = V ∩ {q : a.Y | q ∈ annulus a.Torus} := by
      ext q; constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨by rw [← hVU] at hx; exact hx, x.2⟩
      · rintro ⟨hqV, hq⟩
        exact ⟨⟨q, hq⟩, by rw [← hVU]; exact hqV, rfl⟩
    rw [hEq]
    exact hV.inter (isOpen_annulus a.Torus)
  have hsub : (Subtype.val '' U : Set a.Y) ⊆ innerCore a.Torus := fun q hq => by
    obtain ⟨x, hx, rfl⟩ := hq
    exact x.2.2
  have hW : IsOpen (a.incY '' (Subtype.val '' U)) := isOpen_incY_image a hU' hsub
  have hEq2 : (phiAnnSrc a '' U : Set (Src a))
      = Subtype.val ⁻¹' (a.incY '' (Subtype.val '' U)) := by
    ext z; constructor
    · rintro ⟨q, hq, hqz⟩
      exact ⟨q.1, ⟨q, hq, rfl⟩, congrArg Subtype.val hqz⟩
    · rintro ⟨x, ⟨q, hq, hqx⟩, hxz⟩
      exact ⟨q, hq, Subtype.ext (by show a.incY q.1 = z.1; rw [hqx, hxz])⟩
  rw [hEq2]
  exact hW.preimage continuous_subtype_val

/-- **`A ∩ B` is homeomorphic to the annulus in the filling pieces.** -/
noncomputable def homeoAnnXSrc (a : Assembly) : AnnX a ≃ₜ Src a :=
  (Equiv.ofBijective (phiAnnSrc a) (phiAnnSrc_bijective a)).toHomeomorphOfContinuousOpen
    (continuous_phiAnnSrc a) (isOpenMap_phiAnnSrc a)

/-- **The annulus in the filling pieces is the sigma space `Σ_v AnnPt × T_v`.** -/
noncomputable def homeoAnnXAnnSig (a : Assembly) : AnnX a ≃ₜ AnnSig a :=
  (subtypeSigmaHomeomorph (fun (_ : Cusp) (w : SquarePt × a.Torus _) =>
      1/4 < sqNorm w.1 ∧ sqNorm w.1 < 1)).trans
    (sigmaCongrRightHomeomorph (fun _ =>
      subtypeProdHomeomorph (fun p : SquarePt => 1/4 < sqNorm p ∧ sqNorm p < 1)))

/-- **`A ∩ B` is homotopy equivalent to the glued boundary `⊔_v ∂[-1,1]² × T_v`.** -/
theorem retrAB_homotopyEquiv (a : Assembly) :
    Nonempty (ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}
      (Σ v : Cusp, {p : SquarePt // sqNorm p = 1} × a.Torus v)) :=
  ⟨((homeoAnnXSrc a).symm.toHomotopyEquiv).trans
    ((homeoAnnXAnnSig a).toHomotopyEquiv.trans (heAnnBdry a))⟩

end Work.Space.Split
