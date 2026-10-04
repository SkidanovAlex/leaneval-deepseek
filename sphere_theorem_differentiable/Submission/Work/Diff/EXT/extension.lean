import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.EXT.maximal_regularity
import Submission.Work.Diff.EXT.spliced_jointSmooth
import Submission.Work.Diff.EXT.ricAt_continuousAt

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EXT` area: continuation of the Ricci flow (Hamilton–Shi) — assembly

The contract to be proved is `Extension I M`: a smooth Ricci flow `G` on `[0,T)` whose curvature is
bounded on `[0,T)` extends to a Ricci flow on `[0,T')` for some `T' > T`, agreeing with `G` on
`[0,T)`.  The argument has two halves, following the classical continuation theorem
(Hamilton 1982 §14, Chow–Knopf ch. 7).

**1. Regularity at the maximal time** (`Work.Diff.EXT.maximal_regularity`, a separate, deep
lemma): the family `G` extends to a *jointly smooth* family `G'` on a neighbourhood of `[0,T]`,
with `G' = G` on `[0,T)`.  This is the `C^∞`-convergence step of the continuation theorem: it
requires Shi's local derivative estimates `|∇^k Rm| ≤ C_k` on `[T/2,T)` together with the metric
equivalence `e^{-λt} g(0) ≤ g(t) ≤ e^{λt} g(0)` and bounded-geometry arguments in a fixed atlas.

**2. Restart** (this file).  Write `g_T := G' T` for the limit metric (a smooth metric, since `G'`
is a smooth family).  `ShortTimeExistence` applied to `g_T` produces a Ricci flow `H` on `[0,τ)`
with `H 0 = g_T`.  The spliced family
`W t = if t ≤ T then G' t else H (t - T)`
is then a Ricci flow on `[0, T+τ)` (so one may take `T' = T + τ`), and `W = G` on `[0,T)`.

The assembly of step 2 is carried out below as `extension_of_pieces`, from three inputs:

* `maximal_regularity` — step 1 above;
* `spliced_jointSmooth` — joint smoothness of `W` on `(0, T+τ)`, which is *not* automatic at `t = T`:
  both branches solve the same quasilinear system `∂ₜ g = -2 Ric(g)` and attain the same metric at
  `T`, so their spatial jets at `T` agree and the `t`-jets agree as well; the splice is therefore
  `C^∞` across `t = T` (this is `pde_splice` + `contDiffAt_of_flat_indicator`, filed separately);
* `ricAt_continuousAt` — continuity of the pointwise Ricci tensor along a jointly smooth family,
  used to identify the two-sided `t`-derivative at the seam with `-2 Ric(g_T)`.

Everything below is proved; the only inputs are the displayed lemmas.
-/

-- The model space of the bundle of bilinear forms is `Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) _`,
-- whose `TopologicalSpace` instance is found through `Bundle.ContinuousLinearMap`; with the Shi
-- machinery (`local_ext_closed`, hence the Gram–Schmidt frame family) in scope the default
-- transparency of the instance search is not enough to unfold `Bundle.TotalSpace` to `Sigma` and
-- the search gets stuck.  Turning off `respectTransparency` for definitional equality resolves it.
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- `JointSmooth` is anti-monotone in the time set. -/
theorem JointSmooth.mono {G : ℝ → SMet I M} {J₁ J₂ : Set ℝ} (h : JointSmooth G J₂)
    (hsub : J₁ ⊆ J₂) : JointSmooth G J₁ :=
  ContMDiffOn.mono h (Set.prod_mono hsub (Subset.refl _))

theorem jointSmooth_pairing {G : ℝ → SMet I M} {J : Set ℝ} (hG : JointSmooth G J)
    (x : M) (u v : TangentSpace I x) :
    ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => (G t).inner x u v) J := by
  have hψ : ContMDiffOn 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun t : ℝ ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x ((G t).inner x)) J := by
    have hc : ContMDiffOn 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod I) ∞ (fun t : ℝ ↦ (t, x)) J :=
      contMDiffOn_id.prodMk contMDiffOn_const
    exact hG.comp hc (fun t ht => ⟨ht, trivial⟩)
  have hres := ContMDiffOn.clm_bundle_apply₂ (𝕜 := ℝ)
    (F₁ := E) (E₁ := fun y : M ↦ TangentSpace I y)
    (F₂ := E) (E₂ := fun y : M ↦ TangentSpace I y)
    (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (b := fun _ : ℝ ↦ x) (ψ := fun t : ℝ ↦ (G t).inner x)
    (v := fun _ : ℝ ↦ u) (w := fun _ : ℝ ↦ v) hψ
    (contMDiffOn_const (c := TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) x u))
    (contMDiffOn_const (c := TotalSpace.mk' E (E := fun y : M ↦ TangentSpace I y) x v))
  have hsrc : MapsTo (fun t : ℝ ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
      ((G t).inner x u v)) J (trivializationAt ℝ (Bundle.Trivial M ℝ) x).source :=
    fun _ _ => trivial
  have hiff := (Bundle.Trivialization.contMDiffOn_iff
    (e := trivializationAt ℝ (Bundle.Trivial M ℝ) x)
    (f := fun t : ℝ ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x ((G t).inner x u v))
    hsrc).mp hres
  refine hiff.2.congr fun t _ => ?_
  rw [Bundle.Trivial.eq_trivialization M ℝ (trivializationAt ℝ (Bundle.Trivial M ℝ) x)]
  simp [Bundle.Trivial.trivialization_apply]

theorem jointSmooth_pairing_hasDerivAt {G : ℝ → SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M) (u v : TangentSpace I x) :
    HasDerivAt (fun t : ℝ => (G t).inner x u v) (dtMet G t₀ x u v) t₀ := by
  have h1 : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun t : ℝ => (G t).inner x u v) t₀ :=
    (jointSmooth_pairing hG x u v).contMDiffAt (hJ.mem_nhds ht₀)
  have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => (G t).inner x u v) t₀ := contMDiffAt_iff_contDiffAt.mp h1
  have h3 : DifferentiableAt ℝ (fun t : ℝ => (G t).inner x u v) t₀ := h2.differentiableAt (by simp)
  simpa [dtMet] using h3.hasDerivAt

theorem extension_of_pieces
    (hreg : ∀ (G : ℝ → SMet I M) (T C : ℝ), 0 < T → IsRicciFlow G T →
      (∀ t ∈ Ico 0 T, CurvBound (G t) C) →
      ∃ ε > 0, ∃ G' : ℝ → SMet I M,
        JointSmooth G' (Ioo (-ε) (T + ε)) ∧ ∀ t ∈ Ico 0 T, G' t = G t)
    (hflow_ext : ∀ (G G' : ℝ → SMet I M) (T ε : ℝ), 0 < ε →
      JointSmooth G' (Ioo (-ε) (T + ε)) → (∀ t ∈ Ico 0 T, G' t = G t) → IsRicciFlow G T →
      IsRicciFlow G' T)
    (hsplice : ∀ (G H : ℝ → SMet I M) (T τ ε : ℝ), 0 < ε →
      JointSmooth G (Ioo (T - ε) (T + ε)) → IsRicciFlow G T → IsRicciFlow H τ → H 0 = G T →
      JointSmooth (fun t : ℝ => if t ≤ T then G t else H (t - T)) (Ioo 0 (T + τ)))
    (hric : ∀ (G : ℝ → SMet I M) (J : Set ℝ), IsOpen J → JointSmooth G J →
      ∀ t₀ ∈ J, ∀ (x : M) (u v : TangentSpace I x),
        ContinuousAt (fun t : ℝ => ricAt (lcOf (G t)) x u v) t₀)
    (hSTE : ShortTimeExistence I M) : Extension I M := by
  intro G T C hT hflow hbound
  obtain ⟨ε, hε, G', hGsmooth, hGeq⟩ := hreg G T C hT hflow hbound
  obtain ⟨τ, hτ, H, hHflow, hH0⟩ := hSTE (G' T)
  have hJ : IsOpen (Ioo (-ε) (T + τ)) := isOpen_Ioo
  have hTmem : T ∈ Ioo (-ε) (T + τ) := ⟨by linarith, by linarith⟩
  set W : ℝ → SMet I M := fun t : ℝ => if t ≤ T then G' t else H (t - T) with hWdef
  have hWopen : JointSmooth W (Ioo 0 (T + τ)) := by
    have hGsmooth' : JointSmooth G' (Ioo (T - ε) (T + ε)) :=
      JointSmooth.mono hGsmooth (fun s hs => ⟨by linarith [hs.1, hT], hs.2⟩)
    have hG'flow : IsRicciFlow G' T := hflow_ext G G' T ε hε hGsmooth hGeq hflow
    have h := hsplice G' H T τ ε hε hGsmooth' hG'flow hHflow hH0
    simpa only [hWdef] using h
  -- smoothness on the half-open interval, including the left endpoint `0`
  have hWsm : JointSmooth W (Ico 0 (T + τ)) := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro p hp
    rcases lt_or_eq_of_le hp.1.1 with hpos | hzero
    · exact ⟨Ioo (0:ℝ) (T + τ) ×ˢ (univ : Set M), isOpen_Ioo.prod isOpen_univ,
        ⟨⟨hpos, hp.1.2⟩, trivial⟩, hWopen.mono (fun q hq => hq.2)⟩
    · refine ⟨Ioo (-ε) T ×ˢ (univ : Set M), isOpen_Ioo.prod isOpen_univ,
        ⟨⟨by rw [← hzero]; linarith, by rw [← hzero]; exact hT⟩, trivial⟩, ?_⟩
      refine (hGsmooth.mono ?_).congr ?_
      · intro q hq; exact ⟨⟨hq.2.1.1, by linarith [hq.2.1.2]⟩, trivial⟩
      · intro q hq
        have hqT : q.1 < T := hq.2.1.2
        have hqeq : W q.1 = G' q.1 := by
          simp only [hWdef]; rw [if_pos (le_of_lt hqT)]
        rw [hqeq]
  have hW_eq : ∀ t : ℝ, t ≤ T → W t = G' t := by
    intro t ht; simp only [hWdef]; rw [if_pos ht]
  -- equation on the left half
  have hleft : ∀ t : ℝ, 0 < t → t < T → ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun s : ℝ => (W s).inner x u v) (-2 * ricAt (lcOf (G t)) x u v) t := by
    intro t ht0 htT x u v
    have htT' : t ∈ Ico 0 T := ⟨le_of_lt ht0, htT⟩
    have hbase : HasDerivAt (fun s : ℝ => (G s).inner x u v)
        (-2 * ricAt (lcOf (G t)) x u v) t :=
      (hflow.2 t htT' x u v).hasDerivAt
        (mem_of_superset (Ioo_mem_nhds ht0 htT)
          (fun s hs => ⟨le_of_lt hs.1, hs.2⟩))
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show (0:ℝ) < t from ht0) htT] with s hs
    simp only [hWdef]
    rw [if_pos (le_of_lt hs.2), hGeq s ⟨le_of_lt hs.1, hs.2⟩]
  -- equation on the right half
  have hright : ∀ t : ℝ, T < t → t < T + τ → ∀ (x : M) (u v : TangentSpace I x),
      HasDerivAt (fun s : ℝ => (W s).inner x u v) (-2 * ricAt (lcOf (H (t - T))) x u v) t := by
    intro t hTt htτ x u v
    have hs0 : 0 < t - T := by linarith
    have hsτ : t - T < τ := by linarith
    have hsT : t - T ∈ Ico 0 τ := ⟨le_of_lt hs0, hsτ⟩
    have hbase : HasDerivAt (fun r : ℝ => (H r).inner x u v)
        (-2 * ricAt (lcOf (H (t - T))) x u v) (t - T) :=
      (hHflow.2 (t - T) hsT x u v).hasDerivAt
        (mem_of_superset (Ioo_mem_nhds hs0 hsτ)
          (fun s hs => ⟨le_of_lt hs.1, hs.2⟩))
    have hcomp' : HasDerivAt (fun t' : ℝ => (H (t' - T)).inner x u v)
        (-2 * ricAt (lcOf (H (t - T))) x u v) t := hbase.comp_sub_const t T
    refine hcomp'.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hTt] with s hs
    simp only [hWdef]
    rw [if_neg (not_le.mpr hs)]
  -- the value of the derivative at `T`
  have hvalue : ∀ (x : M) (u v : TangentSpace I x),
      dtMet W T x u v = -2 * ricAt (lcOf (W T)) x u v := by
    intro x u v
    have hpair : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞
        (fun s : ℝ => (W s).inner x u v) (Ioo 0 (T + τ)) := jointSmooth_pairing hWopen x u v
    have hcd : ContDiffOn ℝ ∞ (fun s : ℝ => (W s).inner x u v) (Ioo 0 (T + τ)) :=
      contMDiffOn_iff_contDiffOn.mp hpair
    have hT0 : T ∈ Ioo (0:ℝ) (T + τ) := ⟨hT, by linarith⟩
    have hcontL : ContinuousAt (fun t : ℝ => dtMet W t x u v) T := by
      have h1 : ContinuousOn (deriv (fun s : ℝ => (W s).inner x u v)) (Ioo 0 (T + τ)) :=
        hcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
      have h2 := h1.continuousAt ((isOpen_Ioo : IsOpen (Ioo (0:ℝ) (T + τ))).mem_nhds hT0)
      simpa [dtMet] using h2
    have hcontR : ContinuousAt (fun t : ℝ => -2 * ricAt (lcOf (W t)) x u v) T :=
      (hric W (Ioo 0 (T + τ)) isOpen_Ioo hWopen T hT0 x u v).const_mul (-2)
    haveI hne : (𝓝[Ico (0:ℝ) T] T).NeBot := by
      rw [nhdsWithin_Ico_eq_nhdsLT hT]
      exact nhdsWithin_Iio_neBot le_rfl
    have hev : (fun t : ℝ => dtMet W t x u v)
        =ᶠ[𝓝[Ico (0:ℝ) T] T] (fun t : ℝ => -2 * ricAt (lcOf (W t)) x u v) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Ico (0:ℝ) T ∩ Ioo (T / 2) (T + 1), Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (show T / 2 < T by linarith)
          (show T < T + 1 by linarith))), ?_⟩
      intro t ht
      show dtMet W t x u v = -2 * ricAt (lcOf (W t)) x u v
      have htT' : t < T := ht.1.2
      have ht0 : 0 < t := by linarith [ht.2.1, hT]
      have hder := hleft t ht0 htT' x u v
      have h1 : dtMet W t x u v = -2 * ricAt (lcOf (G t)) x u v := by
        simp only [dtMet]; exact hder.deriv
      have h2 : W t = G t := by
        rw [hW_eq t (le_of_lt htT'), hGeq t ⟨le_of_lt ht0, htT'⟩]
      rw [h1, h2]
    have hlimL : Filter.Tendsto (fun t : ℝ => dtMet W t x u v) (𝓝[Ico (0:ℝ) T] T)
        (𝓝 (dtMet W T x u v)) := hcontL.tendsto.mono_left nhdsWithin_le_nhds
    have hlimR : Filter.Tendsto (fun t : ℝ => -2 * ricAt (lcOf (W t)) x u v) (𝓝[Ico (0:ℝ) T] T)
        (𝓝 (-2 * ricAt (lcOf (W T)) x u v)) := hcontR.tendsto.mono_left nhdsWithin_le_nhds
    have hlimR' : Filter.Tendsto (fun t : ℝ => dtMet W t x u v) (𝓝[Ico (0:ℝ) T] T)
        (𝓝 (-2 * ricAt (lcOf (W T)) x u v)) := Filter.Tendsto.congr' hev.symm hlimR
    exact (tendsto_nhds_unique hlimR' hlimL).symm
  refine ⟨T + τ, by linarith, W, ?_, ?_⟩
  · constructor
    · exact hWsm
    · intro t ht x u v
      rcases lt_trichotomy t T with htT | htT | hTt
      · -- t < T
        have htT' : t ∈ Ico 0 T := ⟨ht.1, htT⟩
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · -- t = 0
          subst h0
          have htT0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_refl 0, hT⟩
          have hbase : HasDerivWithinAt (fun s : ℝ => (G s).inner x u v)
              (-2 * ricAt (lcOf (G 0)) x u v) (Ico 0 T) 0 := hflow.2 0 htT0 x u v
          have h1 : HasDerivWithinAt (fun s : ℝ => (W s).inner x u v)
              (-2 * ricAt (lcOf (G 0)) x u v) (Ico 0 T) 0 := by
            refine hbase.congr (fun s hs => ?_) ?_
            · simp only [hWdef]; rw [if_pos (le_of_lt hs.2), hGeq s hs]
            · simp only [hWdef]; rw [if_pos (le_of_lt hT), hGeq 0 htT0]
          have hfe : 𝓝[Ico (0:ℝ) T] 0 = 𝓝[Ico 0 (T + τ)] 0 := by
            rw [nhdsWithin_Ico_eq_nhdsGE hT, nhdsWithin_Ico_eq_nhdsGE (by linarith)]
          have hmem : Ico (0:ℝ) T ∈ 𝓝[Ico 0 (T + τ)] 0 := hfe ▸ self_mem_nhdsWithin
          have h2 := h1.mono_of_mem_nhdsWithin hmem
          have hval : -2 * ricAt (lcOf (G 0)) x u v = -2 * ricAt (lcOf (W 0)) x u v := by
            rw [hW_eq 0 (le_of_lt hT), hGeq 0 htT0]
          rw [hval] at h2
          exact h2
        · -- 0 < t
          have hder := hleft t h0 htT x u v
          have hval : -2 * ricAt (lcOf (G t)) x u v = -2 * ricAt (lcOf (W t)) x u v := by
            rw [hW_eq t (le_of_lt htT), hGeq t htT']
          rw [hval] at hder
          exact hder.hasDerivWithinAt
      · -- t = T
        rw [htT]
        have hpair := jointSmooth_pairing_hasDerivAt (isOpen_Ioo : IsOpen (Ioo (0:ℝ) (T + τ)))
          hWopen (show T ∈ Ioo (0:ℝ) (T + τ) from ⟨hT, by linarith⟩) x u v
        rw [hvalue x u v] at hpair
        have hmem : Ico (0:ℝ) (T + τ) ∈ 𝓝 T := by
          have h : T ∈ interior (Ico (0:ℝ) (T + τ)) := by
            rw [interior_Ico]; exact ⟨by linarith, by linarith⟩
          exact mem_of_superset (IsOpen.mem_nhds isOpen_interior h) interior_subset
        exact hpair.hasDerivWithinAt
      · -- T < t
        have hder := hright t hTt ht.2 x u v
        have hval : -2 * ricAt (lcOf (H (t - T))) x u v = -2 * ricAt (lcOf (W t)) x u v := by
          simp only [hWdef]
          rw [if_neg (not_le.mpr hTt)]
        rw [hval] at hder
        exact hder.hasDerivWithinAt
  · intro t ht
    rw [hW_eq t (le_of_lt ht.2)]
    exact hGeq t ht

/-- The flow equation transfers to a smooth family agreeing with a flow on `[0,T)`. -/
theorem isRicciFlow_of_eqOn (G G' : ℝ → SMet I M) (T ε : ℝ) (hε : 0 < ε)
    (hG' : JointSmooth G' (Ioo (-ε) (T + ε))) (hEq : ∀ t ∈ Ico 0 T, G' t = G t)
    (hG : IsRicciFlow G T) : IsRicciFlow G' T := by
  refine ⟨JointSmooth.mono hG' (fun t ht => ⟨by linarith [hε, ht.1], by linarith [ht.2, hε]⟩),
    ?_⟩
  intro t ht x u v
  have hval : G' t = G t := hEq t ht
  have hbase := hG.2 t ht x u v
  have hder : -2 * ricAt (lcOf (G t)) x u v = -2 * ricAt (lcOf (G' t)) x u v := by rw [hval]
  rw [hder] at hbase
  exact hbase.congr (fun s hs => by rw [hEq s hs]) (by rw [hval])

/-- **The `EXT` contract**, from the three separate inputs named in the header. -/
theorem extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hSTE : ShortTimeExistence I M)
    (hPP : PinchingPreserved I M) :
    Extension I M :=
  extension_of_pieces maximal_regularity isRicciFlow_of_eqOn spliced_jointSmooth
    (fun G J hJ hG t₀ ht₀ x u v => ricAt_continuousAt hJ hG ht₀ x u v) hSTE

end Work.Diff.EXT
