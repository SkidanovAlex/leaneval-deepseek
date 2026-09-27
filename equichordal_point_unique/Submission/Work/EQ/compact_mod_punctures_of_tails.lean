import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.TailGlueDefs
import Submission.Work.EQ.Tl.isChain_tailGlue
import Submission.Work.EQ.Tl.mem_H0_tailGlue
import Submission.Work.EQ.Tl.junction_at_point
import Submission.Work.EQ.Tl.annulus_glue_bounds
import Submission.Work.EQ.Chart.tailGlue_family_props
import Submission.Work.EQ.Chart.exists_junction_radius
import Submission.Work.EQ.Chart.puncturedChart_covering_family2
import Submission.Work.EQ.finite_zeros_analytic_annulus

/-! # Compactness modulo punctures from the principal tail identities (Rychlik Thm 8(2))

The main theorem of this file is `Work.EQ.compact_mod_punctures_of_tails`.  Its ingredients live
elsewhere in the workspace, because the modules that prove them cannot import this one (this module
holds the definitions the others use):

* `Submission.Work.EQ.TailGlueDefs` : `endFun`, `tailGlue`, `Junction`, `exists_depth`, and the
  fibre lemmas `mem_fibre_eq_candChain`, `fibre_finite_of_annulus`.
* `Submission.Work.EQ.Tl.isChain_tailGlue` : the glued datum is a chain.
* `Submission.Work.EQ.Tl.mem_H0_tailGlue` : the glued family lies in `⁰H`.
* `Submission.Work.EQ.Tl.junction_at_point` : every chain of `S` over the annulus, near a centre
  `z₀`, is a glued chain whose junction identity holds at the corresponding parameter.
* `Submission.Work.EQ.Chart.puncturedChart_covering_family2` : a continuous genuine family of
  chains over a punctured disc is covered by one punctured chart.
* `Submission.Work.EQ.Tl.annulus_glue_bounds`, `Submission.Work.EQ.Chart.tailGlue_family_props`,
  `Submission.Work.EQ.Chart.exists_junction_radius` : copies (in the `Work.EQ.Tl` namespace) of the
  corresponding `Work.EQ.Chart` lemmas; the copies are needed because those modules import this
  one, so this module cannot import them.
* `Submission.Work.EQ.AnnulusCover` : `ac_CompactModPunctures_of_annulus_cover`, the transport from
  an annulus cover to all compact subsets of `ℂ*`.
-/

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- **A compact set is covered by finitely many balls centred at its own points**, with prescribed
positive radii `R z > 0`.  Every centre lies in the compact set. -/
theorem exists_finite_ball_cover {s : Set ℂ} (hs : IsCompact s) {R : ℂ → ℝ}
    (hR : ∀ z ∈ s, 0 < R z) :
    ∃ T : Finset ℂ, (↑T : Set ℂ) ⊆ s ∧ s ⊆ ⋃ z ∈ (T : Set ℂ), Metric.ball z (R z) := by
  obtain ⟨T, hT⟩ := hs.elim_finite_subcover
    (fun z : {z : ℂ // z ∈ s} => Metric.ball (z : ℂ) (R (z : ℂ)))
    (fun z => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩,
      by rw [Metric.mem_ball, dist_self]; exact hR x hx⟩)
  refine ⟨T.image (fun z : {z : ℂ // z ∈ s} => (z : ℂ)), ?_, ?_⟩
  · intro z hz
    obtain ⟨z', -, hz'eq⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    rw [← hz'eq]
    exact Subtype.property z'
  · intro x hx
    obtain ⟨z', hz'T, hdist⟩ := Set.mem_iUnion₂.mp (hT hx)
    exact Set.mem_iUnion₂.mpr ⟨(z' : ℂ),
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z', hz'T, rfl⟩), hdist⟩


/-- **Compactness modulo punctures from the principal tail identities (Rychlik Thm 8(2)).**

`S ⊆ ⁰H` is a union of connected components of `⁰H` on which the invariant parameter
`ψ = ψ₁ψ₂` is the constant `c ≠ 0`, and `S` is invariant under the shift `σ = hShift a`.  Over
some annulus `Ann r₁ r₂` of ratio `> 1/λ`, small enough in the germ radius `r` as scaled by the
depth `N` (`λ^N r₂ < r`, `λ^N ‖c‖/r₁ < r`), every chain of `S` with `ψ₁` in the annulus has its
*principal tails* from depth `N`: forward the stable germ, backward the unstable germ.  Then `S` is
compact modulo finitely many punctures over compact subsets of `ℂ*`.

The hypothesis is the *tail identity* from depth `N`, not merely a "reading" of the two ends
(`q 0 = fan ε ψ₁`, `q (-N) = eqMirror (fan η (λ^N ψ₂))`): the reading form is false, since the
intermediate fan points are total in `h` while `IsStableGerm a h r` constrains `h` only near `0`.
The tail form is the conclusion of `Work.EQ.minimal_cycle_data`, so the caller supplies it.

Route (Rychlik, *Invent. Math.* **129** (1997), Thm 8(2); `PAPER_PROOFS.md` §5 step 4).
* *Annulus to `ℂ*`.*  For compact `K ⊂ ℂ*` the sets `λ^j K` cover a fixed annulus; by
  `Work.EQ.exists_finset_zpow_annulus` finitely many integer shifts `σ^j = shiftZ a j` carry
  `S ∩ {ψ₁ ∈ K}` into `S ∩ {ψ₁ ∈ Ann r₁ r₂}`, and shifts transport punctured charts
  (`ψ₁` and `κ` scale by `λ^j`).  So it suffices to cover `S ∩ {ψ₁ ∈ Ann r₁ r₂}`.
  (A previous prover had proved this transport step as `CompactModPunctures_of_annulus_cover`; its
  module has since been withdrawn, so this step must be redone here.)
* *The band is a finite union of explicit analytic curves.*  `Work.EQ.chain_eq_candChain_of_tails`
  (already proved) turns the tail identities into `q = candChain a h ε η s N c (ψ₁ q)` with
  `(ε,η,s)` of length `N` (`ψ₂ = c/ψ₁` follows from `hval` and `hc`).  Hence, over the annulus, `S`
  is contained in the union of the images of the finitely many maps
  `φ : z ↦ candChain a h ε η s N c z` (at most `2^N·2^N·2^N` of them).
* *Charts.*  Each `φ` has `(φ z).2.1 = z` and is analytic in `z` (each chain coordinate is
  meromorphic).  Where `φ` is locally injective it is itself a `k = 1` punctured chart after
  rescaling to `Metric.ball 0 1`; at a degenerate point `z₀` invert the local expansion with
  `Work.EQ.backward_puiseux` to get `z = z₀ + κ ζ^k` and the chart given by the inverse branch.
  Degenerate points are locally finite, hence finite on the compact annulus.
* *Compact part.*  The finitely many centre points `φ(z₀)` (which a punctured chart does not cover)
  together with the compact image of the annulus minus the finitely many discs give the compact
  `C ⊆ ⁰H`.

Do NOT import `Submission.Work.EQ.exists_compact_regular_cycle` (circular). -/
theorem compact_mod_punctures_of_tails {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) {S : Set ChainData} {c : ℂ}
    (hS : S ⊆ H0 a h) (hc : c ≠ 0) (hval : ∀ q ∈ S, q.2.1 * q.2.2 = c)
    (hclosed : ∀ q ∈ S, ∀ q' ∈ connectedComponentIn (H0 a h) q, q' ∈ S)
    (hcyc : ∀ q : ChainData, q ∈ S ↔ hShift a q ∈ S)
    (htail : ∃ (r₁ r₂ : ℝ) (N : ℕ), 0 < r₁ ∧ r₁ < r₂ ∧ r₂ / r₁ > 1 / eqLam a ∧
      (eqLam a : ℝ) ^ N * r₂ < r ∧ (eqLam a : ℝ) ^ N * ‖c‖ / r₁ < r ∧
      ∀ q ∈ S, q.2.1 ∈ Ann r₁ r₂ →
        (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
        (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2))) :
    CompactModPunctures a h S := by
  classical
  obtain ⟨r₁, r₂, N, hr₁, hr₂, hratio, -, -, htail'⟩ := htail
  -- ## the data of the stable germ
  obtain ⟨ρg, hρg, hgan, hg0, hgreg, hginj, hgd⟩ := germC_facts ha0 ha1 hh
  -- ## a depth at which the germ is uniformly small on the annulus
  obtain ⟨dep, hdepN, hdep1, hbd₁, hbd₂⟩ := exists_depth (c := c) ha0 ha1 hr₁ hr₂ (N := N) hρg
  -- ## it suffices to cover `S` over the annulus
  refine ac_CompactModPunctures_of_annulus_cover ha0 ha1 hcyc hr₁ hr₂ hratio ?_
  -- ### the multiplier
  have hlampos : 0 < eqLam a := eqLam_pos_of ha0 ha1
  have hnorm_lam : ∀ (n : ℕ) (v : ℂ),
      ‖((eqLam a : ℝ) : ℂ) ^ n * v‖ = (eqLam a) ^ n * ‖v‖ := by
    intro n v
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hlampos.le]
  -- ### `endFun a h dep` is analytic on the unit ball around every point of the annulus
  have hend_of : ∀ z ∈ Ann r₁ r₂, AnalyticOnNhd ℂ (endFun a h dep) (Metric.ball z 1) := by
    intro z hz
    have hmap : Set.MapsTo (fun u : ℂ => ((eqLam a : ℝ) : ℂ) ^ dep * u) (Metric.ball z 1)
        (Metric.ball 0 ρg) := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right]
      have hu1 : ‖u - z‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hu
      have h1 : ‖u‖ ≤ ‖z‖ + 1 := by
        have h2 := norm_add_le (u - z) z
        rw [sub_add_cancel] at h2
        linarith
      calc ‖((eqLam a : ℝ) : ℂ) ^ dep * u‖ = (eqLam a) ^ dep * ‖u‖ := hnorm_lam dep u
        _ ≤ (eqLam a) ^ dep * (‖z‖ + 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (eqLam a) ^ dep * (r₂ + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [hz.2]) (by positivity)
        _ < ρg := hbd₁
    have hlin : AnalyticOnNhd ℂ (fun u : ℂ => ((eqLam a : ℝ) : ℂ) ^ dep * u) (Metric.ball z 1) :=
      analyticOnNhd_const.mul analyticOnNhd_id
    have hcomp := hgan.comp hlin hmap
    exact hcomp
  -- ### the unstable-leaf argument stays in the germ ball at every point of the annulus
  have hbnd_of : ∀ z ∈ Ann r₁ r₂, ‖((eqLam a : ℝ) : ℂ) ^ dep * (c / z)‖ < ρg := by
    intro z hz
    have h1 : ‖c / z‖ ≤ ‖c‖ / r₁ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg c) hr₁ hz.1
    have h2 : ‖c‖ / r₁ ≤ 2 * ‖c‖ / r₁ := by
      rw [mul_div_assoc]
      linarith [div_nonneg (norm_nonneg c) hr₁.le]
    rw [hnorm_lam]
    calc (eqLam a) ^ dep * ‖c / z‖ ≤ (eqLam a) ^ dep * (‖c‖ / r₁) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (eqLam a) ^ dep * (2 * ‖c‖ / r₁) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ < ρg := hbd₂
  have hnonzero : ∀ z ∈ Ann r₁ r₂, z ≠ 0 := by
    intro z hz h0
    have hz0 : ‖z‖ = 0 := by rw [h0]; simp
    linarith [hz.1, hr₁, hz0]
  -- ### the junction radius at each centre
  have hjrex : ∀ z : {z : ℂ // z ∈ Ann r₁ r₂}, ∃ r₀ : ℝ, 0 < r₀ ∧
      r₀ ≤ rhoFin' a (endFun a h dep) (z : ℂ) 1 (2 * dep) ∧
      ∀ (σ : Fin (2 * dep) → Bool), Adm a (endFun a h dep) (z : ℂ) 1 σ → ∀ t₀ : ℂ,
        0 < ‖t₀‖ → ‖t₀‖ < r₀ →
        branchPt a (endFun a h dep) (z : ℂ) 1 σ t₀ ⟨0, by omega⟩ =
          ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / ((z : ℂ) + t₀ ^ (2 ^ (2 * dep))))) →
        ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < r₀ →
          branchPt a (endFun a h dep) (z : ℂ) 1 σ t ⟨0, by omega⟩ =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / ((z : ℂ) + t ^ (2 ^ (2 * dep))))) :=
    fun z => Chart.exists_junction_radius ha0 ha1 (hnonzero z z.2) hdep1 (hend_of z z.2) hρg hgan
      (hbnd_of z z.2)
  let jr : ℂ → ℝ := fun z => if hz : z ∈ Ann r₁ r₂ then (hjrex ⟨z, hz⟩).choose else 1
  have hjr : ∀ z (hz : z ∈ Ann r₁ r₂), 0 < jr z ∧
      jr z ≤ rhoFin' a (endFun a h dep) z 1 (2 * dep) ∧
      ∀ (σ : Fin (2 * dep) → Bool), Adm a (endFun a h dep) z 1 σ → ∀ t₀ : ℂ,
        0 < ‖t₀‖ → ‖t₀‖ < jr z →
        branchPt a (endFun a h dep) z 1 σ t₀ ⟨0, by omega⟩ =
          ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z + t₀ ^ (2 ^ (2 * dep))))) →
        ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < jr z →
          branchPt a (endFun a h dep) z 1 σ t ⟨0, by omega⟩ =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z + t ^ (2 ^ (2 * dep))))) := by
    intro z hz
    have h := (hjrex ⟨z, hz⟩).choose_spec
    simpa only [jr, dif_pos hz] using h
  -- ### the usable radius at each centre
  let cap : ℝ := (r₁ / 2) ^ (((2 ^ (2 * dep) : ℕ) : ℝ))⁻¹
  let ρs : ℂ → ℝ := fun z =>
    min (min (rhoFin' a (endFun a h dep) z 1 (2 * dep)) (jr z)) (min 1 cap)
  have hρs_pos : ∀ z (hz : z ∈ Ann r₁ r₂), 0 < ρs z := by
    intro z hz
    refine lt_min (lt_min ?_ (hjr z hz).1) (lt_min one_pos ?_)
    · exact rhoFin'_pos one_pos (hend_of z hz)
    · exact Real.rpow_pos_of_pos (by linarith) _
  have hρs_fin : ∀ z (hz : z ∈ Ann r₁ r₂),
      ρs z ≤ rhoFin' a (endFun a h dep) z 1 (2 * dep) :=
    fun z _ => le_trans (min_le_left _ _) (min_le_left _ _)
  have hρs_jr : ∀ z (hz : z ∈ Ann r₁ r₂), ρs z ≤ jr z :=
    fun z _ => le_trans (min_le_left _ _) (min_le_right _ _)
  have hρs_one : ∀ z (hz : z ∈ Ann r₁ r₂), ρs z ≤ 1 :=
    fun z _ => le_trans (min_le_right _ _) (min_le_left _ _)
  have hρs_cap : ∀ z (hz : z ∈ Ann r₁ r₂), ρs z ≤ cap :=
    fun z _ => le_trans (min_le_right _ _) (min_le_right _ _)
  have hρs_pow : ∀ z (hz : z ∈ Ann r₁ r₂), (ρs z) ^ (2 ^ (2 * dep)) ≤ r₁ / 2 := by
    intro z hz
    exact rpow_bound (X := r₁ / 2) (ρ := ρs z) (by linarith) (hρs_pos z hz).le (by positivity)
      (hρs_cap z hz)
  -- ### the uniform smallness bounds on the disc of radius `ρs z`
  have hbd : ∀ z (hz : z ∈ Ann r₁ r₂), z ≠ 0 ∧
      (∀ t : ℂ, ‖t‖ < ρs z → z + t ^ (2 ^ (2 * dep)) ≠ 0) ∧
      (∀ t : ℂ, ‖t‖ < ρs z →
        ‖((eqLam a : ℝ) : ℂ) ^ dep * (z + t ^ (2 ^ (2 * dep)))‖ < ρg) ∧
      (∀ t : ℂ, ‖t‖ < ρs z →
        ‖((eqLam a : ℝ) : ℂ) ^ dep * (c / (z + t ^ (2 ^ (2 * dep))))‖ < ρg) :=
    fun z hz => Tl.annulus_glue_bounds ha0 ha1 hr₁ hdep1 hbd₁ hbd₂ hz (hρs_pos z hz)
      (hρs_one z hz) (hρs_pow z hz)
  have hbd' : ∀ z (hz : z ∈ Ann r₁ r₂) (t : ℂ), ‖t‖ < ρs z →
      (eqLam a) ^ dep * ‖z + t ^ (2 ^ (2 * dep))‖ < ρg := by
    intro z hz t ht
    have h := (hbd z hz).2.2.1 t ht
    rwa [hnorm_lam] at h
  have hbd'' : ∀ z (hz : z ∈ Ann r₁ r₂) (t : ℂ), ‖t‖ < ρs z →
      (eqLam a) ^ dep * ‖c / (z + t ^ (2 ^ (2 * dep)))‖ < ρg := by
    intro z hz t ht
    have h := (hbd z hz).2.2.2 t ht
    rwa [hnorm_lam] at h
  -- ### the finite disc cover of the annulus
  let R : ℂ → ℝ := fun z => (ρs z / 2) ^ (2 ^ (2 * dep))
  have hRpos : ∀ z (hz : z ∈ Ann r₁ r₂), 0 < R z := fun z hz =>
    pow_pos (by linarith [hρs_pos z hz]) _
  obtain ⟨T, hTsub, hTcov⟩ := exists_finite_ball_cover (isCompact_ann r₁ r₂) hRpos
  let C : Set ChainData := ⋃ z ∈ (T : Set ℂ), {q : ChainData | q ∈ S ∧ q.2.1 = z}
  have hCfin : C.Finite := by
    refine Set.Finite.biUnion T.finite_toSet ?_
    intro z hz
    exact fibre_finite_of_annulus ha0 ha1 hS hval htail' (hTsub (Finset.mem_coe.mp hz))
  have hCcpt : IsCompact C := hCfin.isCompact
  have hCH0 : C ⊆ H0 a h := by
    intro q hq
    obtain ⟨z, -, hmem⟩ := Set.mem_iUnion₂.mp hq
    exact hS hmem.1
  -- ### the finite family of punctured charts
  let Pairs : Finset (ℂ × (Fin (2 * dep) → Bool)) :=
    (T.product (Finset.univ : Finset (Fin (2 * dep) → Bool))).filter
      (fun p => Adm a (endFun a h dep) p.1 1 p.2 ∧ Junction a h c p.1 dep p.2 (ρs p.1))
  let Idx : Type := {p : ℂ × (Fin (2 * dep) → Bool) // p ∈ Pairs}
  haveI : Fintype Idx := Pairs.finite_toSet.fintype
  let m : ℕ := Fintype.card Idx
  let enc : Idx ≃ Fin m := Fintype.equivFin Idx
  have hchartex : ∀ i : Idx, ∃ (e : ℂ → ChainData) (u₀ : ℂ) (k' : ℕ),
      IsPuncturedChart a h e u₀ k' ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρs i.1.1 / 2 →
        tailGlue a h c i.1.1 dep i.1.2 t ∈ e '' (Metric.ball (0 : ℂ) (1 / 2) \ {0}) := by
    intro i
    obtain ⟨hp, hAdm, hJun⟩ := Finset.mem_filter.mp i.2
    obtain ⟨hzT, -⟩ := Finset.mem_product.mp hp
    have hzAnn : i.1.1 ∈ Ann r₁ r₂ := hTsub hzT
    have hbnd := hbd i.1.1 hzAnn
    obtain ⟨hcont, hmer, hmer3⟩ := Chart.tailGlue_family_props ha0 ha1 (cc := c) (z₀ := i.1.1)
      (dep := dep) (σ := i.1.2) hAdm (hend_of i.1.1 hzAnn) (hρs_pos i.1.1 hzAnn)
      (hρs_fin i.1.1 hzAnn) hρg hgan (fun t ht => hbnd.2.1 t ht) (fun t ht => hbnd.2.2.1 t ht)
      (fun t ht => hbnd.2.2.2 t ht)
    have hchain : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρs i.1.1 →
        IsChain a h (tailGlue a h c i.1.1 dep i.1.2 t) := by
      intro t ht0 htρ
      exact Tl.isChain_tailGlue ha0 ha1 hc hρg hgan (fun u hu => (hgreg u hu).1) (hend_of i.1.1 hzAnn)
        (hbd' i.1.1 hzAnn t htρ) (hbd'' i.1.1 hzAnn t htρ) (hbnd.2.1 t htρ) hAdm
        (lt_of_lt_of_le htρ (hρs_fin i.1.1 hzAnn)) (norm_pos_iff.mp ht0) (hJun t ht0 htρ)
    have hmem : ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρs i.1.1 →
        tailGlue a h c i.1.1 dep i.1.2 t ∈ H0 a h :=
      fun t ht0 htρ =>
        Tl.mem_H0_tailGlue ha0 ha1 hbnd.1 hdep1 (hρs_pos i.1.1 hzAnn) hcont ht0 htρ hchain
    exact Chart.puncturedChart_covering_family2 ha0 ha1 hh hbnd.1 Nat.one_le_two_pow
      (hρs_pos i.1.1 hzAnn) hcont hmem (fun t _ _ => tailGlue_psi1 a h c i.1.1 dep i.1.2 t)
      (fun n => (hmer n).1) (fun n => (hmer n).2) hmer3
  choose e u₀ k' hchart hcov using hchartex
  refine ⟨C, m, (fun i => e (enc.symm i)), (fun i => u₀ (enc.symm i)), (fun i => k' (enc.symm i)),
    hCcpt, hCH0, ?_, ?_⟩
  · intro i
    exact hchart (enc.symm i)
  · rintro q ⟨hqS, hqA⟩
    obtain ⟨z, hzT, hzdist⟩ := Set.mem_iUnion₂.mp (hTcov hqA)
    by_cases hqz : q.2.1 = z
    · left
      exact Set.mem_iUnion₂.mpr ⟨z, Finset.mem_coe.mpr hzT, hqS, hqz⟩
    · right
      have hzAnn : z ∈ Ann r₁ r₂ := hTsub hzT
      have hbnd := hbd z hzAnn
      rw [Metric.mem_ball, dist_eq_norm] at hzdist
      have hzdist' : ‖q.2.1 - z‖ < (ρs z / 2) ^ (2 ^ (2 * dep)) := hzdist
      have hqr : ‖q.2.1 - z‖ <
          (rhoFin' a (endFun a h dep) z 1 (2 * dep)) ^ (2 ^ (2 * dep)) := by
        calc ‖q.2.1 - z‖ < (ρs z / 2) ^ (2 ^ (2 * dep)) := hzdist'
          _ ≤ (ρs z) ^ (2 ^ (2 * dep)) :=
              pow_le_pow_left₀ (by linarith [hρs_pos z hzAnn]) (by linarith [hρs_pos z hzAnn]) _
          _ ≤ (rhoFin' a (endFun a h dep) z 1 (2 * dep)) ^ (2 ^ (2 * dep)) :=
              pow_le_pow_left₀ (hρs_pos z hzAnn).le (hρs_fin z hzAnn) _
      obtain ⟨σ, t, hAdm, htk, ht0, -, hqtg, hjun⟩ :=
        Tl.junction_at_point ha0 ha1 hh hS hc hval hr₁ hr₂ htail' hzAnn hdepN hdep1
          (hend_of z hzAnn) hqS hqA hqz hqr
      have htq : ‖t‖ ^ (2 ^ (2 * dep)) < (ρs z / 2) ^ (2 ^ (2 * dep)) := by
        rw [← norm_pow, htk]
        exact hzdist'
      have htnorm : ‖t‖ < ρs z / 2 :=
        (pow_lt_pow_iff_left₀ (norm_nonneg t) (by linarith [hρs_pos z hzAnn]) (by positivity)).mp htq
      have hjunJ : Junction a h c z dep σ (ρs z) := fun t' ht'0 ht'ρ =>
        (hjr z hzAnn).2.2 σ hAdm t ht0 (by linarith [hρs_jr z hzAnn]) hjun
          t' ht'0 (lt_of_lt_of_le ht'ρ (hρs_jr z hzAnn))
      have hmemPairs : (z, σ) ∈ Pairs := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzT, Finset.mem_univ σ⟩, hAdm, hjunJ⟩
      let i₀ : Idx := ⟨(z, σ), hmemPairs⟩
      obtain ⟨ζ, hζ, hζeq⟩ := hcov i₀ t ht0 htnorm
      refine Set.mem_iUnion.mpr ⟨enc i₀, ?_⟩
      rw [Set.mem_image]
      refine ⟨ζ, hζ, ?_⟩
      show e (enc.symm (enc i₀)) ζ = q
      rw [enc.symm_apply_apply i₀]
      exact hζeq.trans hqtg.symm


end

end Work.EQ
