import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts

-- proved helpers (HORN area, sessions before this one)
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germF0_conj1
import Submission.Work.Horn.basin_rescale
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.simplyConnectedSpace_rescale
import Submission.Work.Horn.pushdown_covering
import Submission.Work.Horn.cov_of_parts
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.HornTopo.horn_topo
import Submission.Work.HornPhi.horn_phi
import Submission.Work.HornVarphi.horn_varphi
import Submission.Work.HornSC.horn_sc
import Submission.Work.BasinSC.basin_sc
import Submission.Work.PlanarSC.planar_inter_sc

-- the HB pieces (siblings; HB4 is the covering/LF properness rung)
import Submission.Work.Horn.HB.pushdown_LF
import Submission.Work.Horn.HB.proper_of_covering_LF
import Submission.Work.Horn.HB.basin_of_tower

-- rescaling transports (children of this session)
import Submission.Work.Horn.HBb.Dprime_rescale
import Submission.Work.Horn.HBb.covering_rescale
import Submission.Work.Horn.HBb.LF_rescale

/-! HB6 of the HORN decomposition (`Submission/Work/Horn/HB/DESIGN.md`): the assembly of
Shishikura's Lemma 5.4 basin clause from

* `Work.Horn.HB.pushdown_LF` (HB3: finite local monodromy of `g = pushdown d.E` over its critical
  value `v = π (Φ c)`),
* `Work.Horn.HB.proper_of_covering_LF` (HB4: a covering of a simply connected base which is locally
  finite over the critical value is proper),
* `Work.Horn.HB.basin_of_tower` (HB5: the Shishikura tower over a petal of a parabolic germ),

applied to the rescaled germ `ζ ↦ s * g (ζ / s)` (`s = g''(0)/2`), which is a parabolic germ, and
transported back along the linear change of variables.
-/

namespace Work.Horn

open MandelDim Set Metric Filter Topology

noncomputable section

/-- Transport of the base set of the covering under the rescaling `ζ ↦ s * ζ`. -/
theorem image_mul_baseSet {s v : ℂ} (hs : s ≠ 0) :
    (fun ζ : ℂ => s * ζ) '' {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v} = {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ s * v} := by
  ext w
  constructor
  · rintro ⟨z, ⟨hz0, hzv⟩, rfl⟩
    refine ⟨mul_ne_zero hs hz0, fun h => hzv ?_⟩
    exact mul_left_cancel₀ hs h
  · rintro ⟨hw0, hwv⟩
    refine ⟨w / s, ⟨div_ne_zero hw0 hs, fun h => hwv ?_⟩, by field_simp⟩
    rw [← h]; field_simp

/-- The image of the image of `P` under `ζ ↦ s⁻¹ * ζ` after `ζ ↦ s * ζ` is `P`. -/
theorem mul_inv_image_image {s : ℂ} (hs : s ≠ 0) (P : Set ℂ) :
    (fun ζ : ℂ => s⁻¹ * ζ) '' ((fun ζ : ℂ => s * ζ) '' P) = P := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    simpa only [← mul_assoc, inv_mul_cancel₀ hs, one_mul] using hv
  · intro hw
    refine ⟨s * w, ⟨w, hw, rfl⟩, ?_⟩
    show s⁻¹ * (s * w) = w
    rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- Connected components are transported by the rescaling `ζ ↦ s * ζ`. -/
theorem image_connectedComponentIn_mul {s : ℂ} (hs : s ≠ 0) {P : Set ℂ} {z : ℂ} :
    (fun ζ : ℂ => s * ζ) '' connectedComponentIn P z
      = connectedComponentIn ((fun ζ : ℂ => s * ζ) '' P) (s * z) := by
  by_cases hz : z ∈ P
  · apply Subset.antisymm
    · exact (continuous_const.mul continuous_id).continuousOn.image_connectedComponentIn_subset hz
    · have hcont : Continuous (fun ζ : ℂ => s⁻¹ * ζ) := continuous_const.mul continuous_id
      have h := hcont.continuousOn.image_connectedComponentIn_subset
        (s := (fun ζ : ℂ => s * ζ) '' P) (a := s * z) (mem_image_of_mem _ hz)
      have hset : connectedComponentIn ((fun ζ : ℂ => s⁻¹ * ζ) ''
            ((fun ζ : ℂ => s * ζ) '' P)) (s⁻¹ * (s * z)) = connectedComponentIn P z := by
        rw [mul_inv_image_image hs P,
          show s⁻¹ * (s * z) = z by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]]
      have h' : (fun ζ : ℂ => s⁻¹ * ζ) ''
          connectedComponentIn ((fun ζ : ℂ => s * ζ) '' P) (s * z) ⊆ connectedComponentIn P z := by
        intro u hu
        have hu' := h hu
        rwa [hset] at hu'
      intro w hw
      refine ⟨s⁻¹ * w, h' ⟨w, hw, rfl⟩, ?_⟩
      show s * (s⁻¹ * w) = w
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  · rw [connectedComponentIn_eq_empty hz, Set.image_empty, connectedComponentIn_eq_empty]
    intro h
    obtain ⟨v, hv, hvs⟩ := h
    have hvz : v = z := mul_left_cancel₀ hs hvs
    exact hz (hvz ▸ hv)

/-- **The conclusion of Lemma 5.4 transported back along the rescaling.**  If `Bt` is a
`g`-invariant, proper, simply connected component of the parabolic basin of the rescaled map
`ζ ↦ s * G (ζ / s)` on `s • D` carrying a critical point of that map, then the corresponding
component of the parabolic basin of `G` on `D` has the same four properties. -/
theorem clause_transport {G : ℂ → ℂ} {D : Set ℂ} {s : ℂ} (hs : s ≠ 0)
    (hbasin : MandelDim.ParabolicBasin (fun ζ : ℂ => s * G (ζ / s)) ((fun ζ : ℂ => s * ζ) '' D)
      = (fun ζ : ℂ => s * ζ) '' (MandelDim.ParabolicBasin G D))
    {Bt : Set ℂ}
    (hBtcomp : ∃ z ∈ MandelDim.ParabolicBasin (fun ζ : ℂ => s * G (ζ / s))
      ((fun ζ : ℂ => s * ζ) '' D),
      Bt = connectedComponentIn (MandelDim.ParabolicBasin (fun ζ : ℂ => s * G (ζ / s))
        ((fun ζ : ℂ => s * ζ) '' D)) z)
    (hBtmap : Set.MapsTo (fun ζ : ℂ => s * G (ζ / s)) Bt Bt)
    (hBtprop : ∀ L : Set ℂ, L ⊆ Bt → IsCompact L →
      IsCompact (Bt ∩ (fun ζ : ℂ => s * G (ζ / s)) ⁻¹' L))
    (hBtsc : SimplyConnectedSpace Bt)
    (hBtcrit : ∃ z ∈ Bt, deriv (fun ζ : ℂ => s * G (ζ / s)) z = 0) :
    ∃ B' : Set ℂ,
      (∃ z ∈ MandelDim.ParabolicBasin G D,
        B' = connectedComponentIn (MandelDim.ParabolicBasin G D) z) ∧
      Set.MapsTo G B' B' ∧
      (∀ L : Set ℂ, L ⊆ B' → IsCompact L → IsCompact (B' ∩ G ⁻¹' L)) ∧
      SimplyConnectedSpace B' ∧ ∃ z ∈ B', deriv G z = 0 := by
  -- the two spellings of the rescaling: `ζ / s = s⁻¹ * ζ`
  have hspell : (fun ζ : ℂ => s * G (ζ / s)) = fun ζ : ℂ => s * G (s⁻¹ * ζ) := by
    funext ζ
    rw [div_eq_inv_mul, mul_comm]
  rw [hspell] at hbasin hBtcomp hBtmap hBtprop hBtcrit
  have hinv_mul : ∀ w : ℂ, s⁻¹ * (s * w) = w := fun w => by
    rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have hmul_inv : ∀ w : ℂ, s * (s⁻¹ * w) = w := fun w => by
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have hmul : ∀ {a b : ℂ}, s * a = s * b → a = b := fun h => mul_left_cancel₀ hs h
  refine ⟨(fun ζ : ℂ => s⁻¹ * ζ) '' Bt, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) it is a component of the parabolic basin of `G` on `D`
    obtain ⟨z, hz, hzBt⟩ := hBtcomp
    obtain ⟨u, huB, huz⟩ : ∃ u ∈ MandelDim.ParabolicBasin G D, s * u = z := by
      have h1 : z ∈ (fun ζ : ℂ => s * ζ) '' (MandelDim.ParabolicBasin G D) := by
        rw [← hbasin]; exact hz
      simpa using h1
    refine ⟨s⁻¹ * z, ?_, ?_⟩
    · rw [← huz, hinv_mul]
      exact huB
    · rw [hzBt, image_connectedComponentIn_mul (inv_ne_zero hs)
        (P := MandelDim.ParabolicBasin (fun ζ : ℂ => s * G (s⁻¹ * ζ))
          ((fun ζ : ℂ => s * ζ) '' D)) (z := z), hbasin,
        mul_inv_image_image hs (MandelDim.ParabolicBasin G D)]
  · -- (2) `G` maps it to itself
    rintro w ⟨u, hu, rfl⟩
    exact ⟨s * G (s⁻¹ * u), hBtmap hu, hinv_mul _⟩
  · -- (3) properness
    intro L hLB hLc
    have hLs : (fun ζ : ℂ => s * ζ) '' L ⊆ Bt := by
      rintro x ⟨w, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hLB hw
      show s * (s⁻¹ * v) ∈ Bt
      rw [hmul_inv]
      exact hv
    have hcomp : IsCompact (Bt ∩ (fun ζ : ℂ => s * G (s⁻¹ * ζ)) ⁻¹'
        ((fun ζ : ℂ => s * ζ) '' L)) :=
      hBtprop _ hLs (hLc.image (continuous_const.mul continuous_id))
    have hset : (fun ζ : ℂ => s⁻¹ * ζ) '' Bt ∩ G ⁻¹' L
        = (fun ζ : ℂ => s⁻¹ * ζ) ''
            (Bt ∩ (fun ζ : ℂ => s * G (s⁻¹ * ζ)) ⁻¹' ((fun ζ : ℂ => s * ζ) '' L)) := by
      ext w
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hwL⟩
        exact ⟨v, ⟨hv, ⟨G (s⁻¹ * v), hwL, rfl⟩⟩, rfl⟩
      · rintro ⟨v, ⟨hv, y, hyL, hyv⟩, rfl⟩
        refine ⟨⟨v, hv, rfl⟩, ?_⟩
        show G (s⁻¹ * v) ∈ L
        have hyv' : s * y = s * G (s⁻¹ * v) := hyv
        rw [← hmul hyv']
        exact hyL
    rw [hset]
    exact hcomp.image (continuous_const.mul continuous_id)
  · -- (4) it is simply connected
    exact Work.Horn.simplyConnectedSpace_rescale (inv_ne_zero hs) hBtsc
  · -- (5) it contains a critical point of `G`
    obtain ⟨u, huBt, hucrit⟩ := hBtcrit
    have hderiv := congrFun (Work.Horn.deriv_rescale_eq G s hs) u
    rw [hspell] at hderiv
    rw [div_eq_inv_mul, mul_comm] at hderiv
    refine ⟨s⁻¹ * u, ⟨u, huBt, rfl⟩, ?_⟩
    have h1 : deriv G (s⁻¹ * u) = deriv G (u * s⁻¹) := by rw [mul_comm]
    rw [h1, ← hderiv]
    exact hucrit

/-- The `D'`-package of the Lemma 5.4 assembly: `D' = {0} ∪ π(B̃ᵘ)` is open, contains `0`, lies in
the horn domain `D_g = {0} ∪ π(B̃ᵘ ∪ B̃ˡ)`, is bounded, and no preconnected subset of `D_g ∖ {0}`
meets `D'` without being contained in it.  All of this is `Work.Horn.Dg_pieces`. -/
theorem Dprime_package {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) :
    IsOpen (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) ∧
    (0 : ℂ) ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) ∧
    insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) ⊆
      insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) ∧
    Bornology.IsBounded (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) ∧
    (∀ C : Set ℂ, IsPreconnected C →
      C ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) \ {0} →
      (C ∩ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))).Nonempty →
      C ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) := by
  obtain ⟨hUo, hUb, -, hUV, -, hcross⟩ := Work.Horn.Dg_pieces hF0 d hB hBne
  refine ⟨hUo, Set.mem_insert _ _, ?_, hUb, ?_⟩
  · rw [hUV]
    exact Set.subset_union_left
  · intro C hC hsub hmeet
    exact hcross C hC (fun z hz => (hsub hz).1) hmeet

/-- **Lemma 5.4, basin clause** (Shishikura, *The Hausdorff dimension of the boundary of the
Mandelbrot set*, Lemma 5.4): the pushed-down horn map `g = pushdown d.E` of an `𝓕₀`-germ has a
`g`-invariant component `B'` of its parabolic basin on `D_g = {0} ∪ π (B̃ᵘ ∪ B̃ˡ)` on which `g` is
proper, which is simply connected and carries a critical point of `g`. -/
theorem horn_basin_thm {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) :
    MandelDim.HornBasinClause d := by
  classical
  intro hF0 B hB Bu Bl hBu hBl
  -- ## Step 1: the `𝓕₀`-setup and the two end components
  have hBne : B.Nonempty := hB.2.1.1
  obtain ⟨c, hS⟩ := Work.Horn.isF0Setup_of_immediateBasin hF0 d hB hBne
  have hBuOf : Bu = MandelDim.BuOf d B := hBu.trans (Work.Horn.BuOf_eq_component d B).symm
  have hBlOf : Bl = MandelDim.BlOf d B := hBl.trans (Work.Horn.BlOf_eq_component d B).symm
  obtain ⟨hBuO', hBlO', -, -, hupOf, hloOf, hsubOf⟩ :=
    Work.HornTopo.horn_topo f₀ D₀ B c d hS
  have hBuO : IsOpen Bu := by rw [hBuOf]; exact hBuO'
  have hBlO : IsOpen Bl := by rw [hBlOf]; exact hBlO'
  have hup : {w : ℂ | d.η₀ < w.im} ⊆ Bu := fun w hw => by rw [hBuOf]; exact hupOf hw
  have hlo : {w : ℂ | w.im < -d.η₀} ⊆ Bl := fun w hw => by rw [hBlOf]; exact hloOf hw
  have hsub : Bu ∪ Bl ⊆ d.DE := by
    rw [hBuOf, hBlOf]
    exact hsubOf
  -- the horn domain `D_g`, in both spellings
  have hDgeq : insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) =
      insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
    rw [hBuOf, hBlOf]
  -- ## Step 2: the pushed-down horn map `g = pushdown d.E` on `D_g`
  have hsecond : deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 :=
    Work.Horn.pushdown_second_deriv_ne_zero hF0 d hB hBne hBu hBl hsub hup hlo
  have hcovE := Work.Horn.cov_of_parts Work.HornTopo.horn_topo Work.HornPhi.horn_phi
    Work.HornVarphi.horn_varphi Work.Horn.hornSC f₀ D₀ B c d hS
  have hcov : IsCoveringMapOn
      (fun z : ↥(insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) => MandelDim.pushdown d.E z)
      {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ MandelDim.piExp (d.Φ c)} := by
    rw [hDgeq]
    exact Work.Horn.pushdown_covering Work.HornTopo.horn_topo d hS hcovE
  have hcrit : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      deriv (MandelDim.pushdown d.E) z = 0 →
      MandelDim.pushdown d.E z = MandelDim.piExp (d.Φ c) :=
    Work.Horn.pushdown_critval_global_eq hF0 d hB hBne hS hBu hBl hsub hup hlo
  obtain ⟨r, hr, hrv, hLFOf⟩ := Work.Horn.HB.pushdown_LF d hS
  have hLF : ∀ x ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      MandelDim.pushdown d.E x ∈ Metric.ball (MandelDim.piExp (d.Φ c)) r →
      ∀ K ⊆ Metric.ball (MandelDim.piExp (d.Φ c)) r, IsCompact K →
        IsCompact (connectedComponentIn
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) ∩
            MandelDim.pushdown d.E ⁻¹' Metric.ball (MandelDim.piExp (d.Φ c)) r) x ∩
          MandelDim.pushdown d.E ⁻¹' K) := by
    rw [hDgeq]
    exact hLFOf
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    Work.Horn.zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  -- ## Step 3: `D' = {0} ∪ π(B̃ᵘ)` and its rescaling by `s`
  obtain ⟨hD'o, h0D', hD'sub₀, hD'b, hD'comp₀⟩ := Dprime_package hF0 d hB hBne
  have hD'sub : insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) ⊆
      insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    rw [hDgeq]
    exact hD'sub₀
  have hD'comp : ∀ C : Set ℂ, IsPreconnected C →
      C ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) \ {0} →
      (C ∩ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))).Nonempty →
      C ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) := by
    intro C hC hsubC hmeet
    refine hD'comp₀ C hC ?_ hmeet
    intro z hz
    rw [← hDgeq]
    exact hsubC hz
  set s : ℂ := Work.Repel.s0 d with hsdef
  have hs : s ≠ 0 := by
    rw [hsdef, Work.Repel.s0]
    exact div_ne_zero hsecond (by norm_num)
  obtain ⟨hD's_o, hD's_0, hD's_sub₀, hD's_b, hD's_comp₀⟩ :=
    Work.Horn.HBb.Dprime_rescale (D := insert 0
        (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)))
      (D' := insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)))
      (s := s) hs hD'o h0D' hD'sub₀ hD'b hD'comp₀
  have hD's_sub : (fun ζ : ℂ => s * ζ) '' insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) ⊆
      (fun ζ : ℂ => s * ζ) '' insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
    Set.image_mono hD'sub
  -- ## Step 4: the rescaled germ is a parabolic germ
  have hgem : MandelDim.IsParabolicGerm (Work.Repel.germ1 s d.E)
      (Work.Repel.Dgerm1 s (Bu ∪ Bl)) := by
    rw [hsdef]
    exact Work.Horn.isParabolicGerm_germ1 hF0 d hB hBne hBu hBl hsub hup hlo hsecond
  have hcov_s : IsCoveringMapOn
      (fun z : ↥(Work.Repel.Dgerm1 s (Bu ∪ Bl)) => Work.Repel.germ1 s d.E z)
      {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ s * MandelDim.piExp (d.Φ c)} := by
    have h1 := Work.Horn.HBb.covering_rescale (G := MandelDim.pushdown d.E) hs hcov
    rw [image_mul_baseSet hs] at h1
    exact h1
  have hLF_s : ∀ x ∈ (fun ζ : ℂ => s * ζ) '' (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      (fun ζ : ℂ => s * MandelDim.pushdown d.E (ζ / s)) x ∈
        Metric.ball (s * MandelDim.piExp (d.Φ c)) (‖s‖ * r) →
      ∀ K ⊆ Metric.ball (s * MandelDim.piExp (d.Φ c)) (‖s‖ * r), IsCompact K →
        IsCompact (connectedComponentIn
          (((fun ζ : ℂ => s * ζ) '' (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∩
            (fun ζ : ℂ => s * MandelDim.pushdown d.E (ζ / s)) ⁻¹'
              Metric.ball (s * MandelDim.piExp (d.Φ c)) (‖s‖ * r)) x ∩
          (fun ζ : ℂ => s * MandelDim.pushdown d.E (ζ / s)) ⁻¹' K) :=
    Work.Horn.HBb.LF_rescale (G := MandelDim.pushdown d.E) hs hLF
  have h0out_s : (0 : ℂ) ∉ MandelDim.ParabolicBasin (Work.Repel.germ1 s d.E)
      (Work.Repel.Dgerm1 s (Bu ∪ Bl)) := by
    intro h0
    have h0' : (0 : ℂ) ∈ MandelDim.ParabolicBasin (Work.Repel.germ1 s d.E)
        ((fun ζ : ℂ => s * ζ) '' (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) := h0
    refine h0out ((Work.Horn.basin_rescale (s := s) hs d.E
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) 0).mpr ?_)
    simpa using h0'
  -- ## Step 5: HB5 (the tower) for the rescaled germ
  have hD's_comp : ∀ C : Set ℂ, IsPreconnected C →
      C ⊆ (fun ζ : ℂ => s * ζ) '' insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) \ {0} →
      (C ∩ (fun ζ : ℂ => s * ζ) '' insert 0
        (MandelDim.piExp '' (MandelDim.BuOf d B))).Nonempty →
      C ⊆ (fun ζ : ℂ => s * ζ) '' insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) := by
    intro C hC hsubC hmeet
    refine hD's_comp₀ C hC ?_ hmeet
    intro z hz
    rw [← hDgeq]
    exact hsubC hz
  obtain ⟨Bt, hBtcomp, hBtmap, hBtprop, hBtsc, hBtcrit⟩ :=
    Work.Horn.HB.basin_of_tower (g := Work.Repel.germ1 s d.E)
      (D := Work.Repel.Dgerm1 s (Bu ∪ Bl))
      (D' := (fun ζ : ℂ => s * ζ) '' insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)))
      (v := s * MandelDim.piExp (d.Φ c)) (r := ‖s‖ * r)
      hgem (mul_pos (norm_pos_iff.mpr hs) hr)
      (by rw [norm_mul]; exact mul_lt_mul_of_pos_left hrv (norm_pos_iff.mpr hs))
      hcov_s hLF_s hD's_o hD's_sub hD's_0 hD's_b hD's_comp
  -- ## Step 6: transport the conclusion back along `ζ ↦ ζ / s`
  have hbasin : MandelDim.ParabolicBasin (fun ζ : ℂ => s * MandelDim.pushdown d.E (ζ / s))
        ((fun ζ : ℂ => s * ζ) '' (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
      = (fun ζ : ℂ => s * ζ) ''
          (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
            (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) := by
    ext w
    constructor
    · intro hw
      have hws : s * (w / s) = w := by field_simp
      refine ⟨w / s, ?_, hws⟩
      rw [← hws] at hw
      exact (Work.Horn.basin_rescale (s := s) hs d.E
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) (w / s)).mpr hw
    · rintro ⟨z, hz, rfl⟩
      exact (Work.Horn.basin_rescale (s := s) hs d.E
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) z).mp hz
  obtain ⟨B', hB'comp, hB'map, hB'prop, hB'sc, hB'crit⟩ :=
    clause_transport (G := MandelDim.pushdown d.E)
      (D := insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) hs hbasin
      hBtcomp hBtmap hBtprop hBtsc hBtcrit
  exact ⟨B', hB'comp, hB'map, hB'prop, hB'sc, hB'crit⟩

end

end Work.Horn
