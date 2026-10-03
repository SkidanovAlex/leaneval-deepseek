import Mathlib
import Submission.Work.BasinSC.tower
import Submission.Work.BasinSC.cover_basic
import Submission.Work.BasinSC.step
import Submission.Work.BasinSC.Tower.connectedComponentIn_inter_closure
import Submission.Work.BasinSC.Tower.isCompact_connectedComponentIn_inter_preimage

/-!
# The inductive step of the tower (Shishikura, Lemma 5.2)

For the setup `IsF0Setup f₀ D₀ B c` with §4.1 data `d : ParabData f₀ D₀` and the tower

`V n = {z | f₀^[n] z ∈ d.Ωp} ∩ B`,

the map `f₀ : V (n+1) → V n` is holomorphic, proper and surjective, and maps a component of
`V (n+1)` *onto* the component of `V n` through the image point.  This is the structural input to
the inductive step of Lemma 5.2.

The proof rests on two general facts:

* `connectedComponentIn_inter_closure`: a connected component of a subspace `F` is closed in `F`.
* the open mapping theorem for analytic functions (`AnalyticOnNhd.is_constant_or_isOpen`), which
  shows that `f₀ '' C'` is open inside `C` (the restriction of `f₀` to `C'` is not constant because
  `f₀` has at most one critical point in `B`), while the properness of `f₀ : B → B` inherited from
  `IsImmediateBasin` shows it is also closed in `C`; preconnectedness of `C` then gives
  `f₀ '' C' = C`.
-/

open Set Metric Filter Topology MandelDim

namespace Work.BasinSC.Tower

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- The levels of the tower are open in `ℂ`: on the basin `B` the iterates of `f₀` are continuous
(every orbit of a basin point stays in `B ⊆ D₀`, where `f₀` is holomorphic), so the preimage of the
open petal is open. -/
lemma tower_level_open (hF0 : MandelDim.IsF0Setup f₀ D₀ B c)
    (d : MandelDim.ParabData f₀ D₀) (n : ℕ) : IsOpen (Work.BasinSC.tower f₀ B d.Ωp n) := by
  obtain ⟨hgerm, hB, -, -, -⟩ := hF0
  have hBsubD : B ⊆ D₀ := by
    intro z hz
    obtain ⟨U, hU, hiter, -⟩ := hB.2.2.1 hz
    simpa using hiter 0 (mem_of_mem_nhds hU)
  have hmap : MapsTo f₀ B B := hB.2.2.2.2.1
  have hmapit : ∀ k : ℕ, MapsTo (f₀^[k]) B B := by
    intro k
    induction k with
    | zero => intro z hz; exact hz
    | succ j ih => rw [Function.iterate_succ']; exact hmap.comp ih
  have hcont : ∀ k : ℕ, ContinuousOn (f₀^[k]) B := by
    intro k
    induction k with
    | zero => simpa using continuousOn_id
    | succ j ih =>
      rw [Function.iterate_succ']
      exact (hgerm.2.2.1.continuousOn.mono hBsubD).comp ih (hmapit j)
  rw [isOpen_iff_mem_nhds]
  intro z hz
  simp only [Work.BasinSC.tower, mem_inter_iff, mem_ofPred_eq] at hz ⊢
  exact Filter.inter_mem
    (((hcont n).continuousAt (hB.1.mem_nhds hz.2)).preimage_mem_nhds (d.Ωp_open.mem_nhds hz.1))
    (hB.1.mem_nhds hz.2)

/-- The tower satisfies the recursion `V (n+1) = B ∩ f₀ ⁻¹' V n`. -/
lemma tower_succ_eq {B Ωp : Set ℂ} (hmap : MapsTo f₀ B B) (n : ℕ) :
    Work.BasinSC.tower f₀ B Ωp (n+1) = B ∩ f₀ ⁻¹' Work.BasinSC.tower f₀ B Ωp n := by
  ext z
  simp only [Work.BasinSC.tower, mem_inter_iff, mem_ofPred_eq, mem_preimage]
  constructor
  · rintro ⟨hz, hzB⟩
    rw [Function.iterate_succ_apply] at hz
    exact ⟨hzB, hz, hmap hzB⟩
  · rintro ⟨hzB, hz, -⟩
    exact ⟨by rwa [Function.iterate_succ_apply], hzB⟩

-- The structural facts needed for the inductive step of Lemma 5.2: for `x` in the level `n+1` of
-- the tower `V n = {z | f₀^[n] z ∈ Ωp} ∩ B`, writing `C'` for the component of `x` in `V (n+1)` and
-- `C` for the component of `f₀ x` in `V n`, we have: `C'` open, connected; `f₀` differentiable on
-- `C'`; `f₀` maps `C'` into `C`; `f₀` maps `C'` **onto** `C` (`C ⊆ f₀ '' C'`); and the restriction
-- `f₀ : C' → C` is proper (`C' ∩ f₀ ⁻¹' K` compact for `K ⊆ C` compact).
theorem tower_step {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (hF0 : MandelDim.IsF0Setup f₀ D₀ B c)
    (d : MandelDim.ParabData f₀ D₀) (n : ℕ) :
    ∀ x ∈ Work.BasinSC.tower f₀ B d.Ωp (n + 1),
      IsOpen (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp (n + 1)) x) ∧
      IsConnected (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp (n + 1)) x) ∧
      DifferentiableOn ℂ f₀ (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp (n + 1)) x) ∧
      Set.MapsTo f₀ (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp (n + 1)) x)
        (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp n) (f₀ x)) ∧
      (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp n) (f₀ x)) ⊆
        f₀ '' (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp (n + 1)) x) ∧
      (∀ K ⊆ connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp n) (f₀ x), IsCompact K →
        IsCompact (connectedComponentIn (Work.BasinSC.tower f₀ B d.Ωp (n + 1)) x ∩
          f₀ ⁻¹' K)) := by
  intro x hx
  have hF0c := hF0
  obtain ⟨hgerm, hB, hcB, hderivc, huniq⟩ := hF0
  have hBsubD : B ⊆ D₀ := by
    intro z hz
    obtain ⟨U, hU, hiter, -⟩ := hB.2.2.1 hz
    simpa using hiter 0 (mem_of_mem_nhds hU)
  have hmap : MapsTo f₀ B B := hB.2.2.2.2.1
  have hBproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f₀ ⁻¹' L) := hB.2.2.2.2.2.2
  have hBopen : IsOpen B := hB.1
  have hD0open : IsOpen D₀ := hgerm.1
  have hf0diffD : DifferentiableOn ℂ f₀ D₀ := hgerm.2.2.1
  have hf0contB : ContinuousOn f₀ B := hf0diffD.continuousOn.mono hBsubD
  set V := Work.BasinSC.tower f₀ B d.Ωp (n+1) with hVdef
  set W := Work.BasinSC.tower f₀ B d.Ωp n with hWdef
  have hVopen : IsOpen V := by rw [hVdef]; exact tower_level_open hF0c d (n+1)
  have hWopen : IsOpen W := by rw [hWdef]; exact tower_level_open hF0c d n
  have hVeq : V = B ∩ f₀ ⁻¹' W := by rw [hVdef, hWdef]; exact tower_succ_eq hmap n
  have hVsubB : V ⊆ B := by rw [hVdef]; exact inter_subset_right
  have hWsubB : W ⊆ B := by rw [hWdef]; exact inter_subset_right
  have hxV : x ∈ V := by rw [hVdef]; exact hx
  have hfxW : f₀ x ∈ W := by
    have h2 : (f₀^[n]) (f₀ x) ∈ d.Ωp := by
      have h3 : (f₀^[n+1]) x ∈ d.Ωp := hx.1
      rwa [Function.iterate_succ_apply] at h3
    rw [hWdef]
    exact ⟨h2, hmap hx.2⟩
  set C' := connectedComponentIn V x with hC'def
  set C := connectedComponentIn W (f₀ x) with hCdef
  have hC'open : IsOpen C' := by rw [hC'def]; exact hVopen.connectedComponentIn
  have hC'pre : IsPreconnected C' := by rw [hC'def]; exact isPreconnected_connectedComponentIn
  have hC'conn : IsConnected C' := by
    rw [hC'def]; exact isConnected_connectedComponentIn_iff.mpr hxV
  have hC'ne : C'.Nonempty := by rw [hC'def]; exact ⟨x, mem_connectedComponentIn hxV⟩
  have hC'cl : C' = V ∩ closure C' := by rw [hC'def]; exact connectedComponentIn_inter_closure
  have hC'subV : C' ⊆ V := by rw [hC'def]; exact connectedComponentIn_subset V x
  have hC'subB : C' ⊆ B := hC'subV.trans hVsubB
  have hC'subD : C' ⊆ D₀ := hC'subB.trans hBsubD
  have hC'diff : DifferentiableOn ℂ f₀ C' := hf0diffD.mono hC'subD
  have hCopen : IsOpen C := by rw [hCdef]; exact hWopen.connectedComponentIn
  have hCpre : IsPreconnected C := by rw [hCdef]; exact isPreconnected_connectedComponentIn
  have hfxC : f₀ x ∈ C := by rw [hCdef]; exact mem_connectedComponentIn hfxW
  -- The restriction of `f₀` to `C'` is proper over `C`: this is inherited from the properness of
  -- `f₀ : B → B` coming from `IsImmediateBasin`, since `C'` is a connected component of
  -- `V = B ∩ f₀ ⁻¹' W`; see `isCompact_connectedComponentIn_inter_preimage`.
  have hproper : ∀ K ⊆ C, IsCompact K → IsCompact (C' ∩ f₀ ⁻¹' K) :=
    isCompact_connectedComponentIn_inter_preimage (f := f₀) (B := B) (W := W) (V := V) (x := x)
      hBproper hWsubB hVeq
  have hcontV : ContinuousOn f₀ V := hf0contB.mono hVsubB
  -- `f₀` maps `C'` into `C`
  have hmapsto : MapsTo f₀ C' C := by
    rw [Set.mapsTo_iff_image_subset]
    have h1 : f₀ '' C' ⊆ connectedComponentIn (f₀ '' V) (f₀ x) :=
      hcontV.image_connectedComponentIn_subset hxV
    have hfVW : f₀ '' V ⊆ W := by
      rintro y ⟨z, hzV, rfl⟩
      exact (hVeq ▸ hzV).2
    exact h1.trans (connectedComponentIn_mono (f₀ x) hfVW)
  -- `f₀ '' C'` is open: the open mapping theorem, using that `f₀` is not constant on `C'` since
  -- `C'` is open and meets `B`, where `f₀` has at most one critical point.
  have hAopen : IsOpen (f₀ '' C') := by
    have hana : AnalyticOnNhd ℂ f₀ C' := (hf0diffD.analyticOnNhd hD0open).mono hC'subD
    rcases hana.is_constant_or_isOpen hC'pre with ⟨w, hw⟩ | hopen
    · exfalso
      have hderiv0 : ∀ z ∈ C', deriv f₀ z = 0 := by
        intro z hz
        have hev : (fun _ : ℂ => w) =ᶠ[𝓝 z] f₀ := by
          filter_upwards [hC'open.mem_nhds hz] with z' hz'
          exact (hw z' hz').symm
        have h1 : deriv (fun _ : ℂ => w) z = deriv f₀ z := hev.deriv_eq
        rw [deriv_const] at h1
        exact h1.symm
      have hsub : C' ⊆ {c} := fun z hz => huniq z (hC'subB hz) (hderiv0 z hz)
      obtain ⟨z0, hz0⟩ := hC'ne
      have hz0c : z0 = c := by simpa using hsub hz0
      have hcs : ({c} : Set ℂ) ⊆ C' := by rw [← hz0c]; exact singleton_subset_iff.mpr hz0
      have : IsOpen ({c} : Set ℂ) := (hsub.antisymm hcs) ▸ hC'open
      exact not_isOpen_singleton c this
    · exact hopen C' subset_rfl hC'open
  -- `f₀ '' C'` is closed in `C`: a limit point `y` of `f₀ '' C'` is the image of a limit point of
  -- `C' ∩ f₀ ⁻¹' K` for a compact `K ∋ y` inside `C`, using properness.
  have hAcl : closure (f₀ '' C') ∩ C ⊆ f₀ '' C' := by
    rintro y ⟨hycl, hyC⟩
    obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall y r ⊆ C := by
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hCopen y hyC
      exact ⟨ρ/2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hρsub⟩
    have hKc : IsCompact (closedBall y r) := isCompact_closedBall y r
    have hE : IsCompact (C' ∩ f₀ ⁻¹' closedBall y r) := hproper _ hrsub hKc
    have hEc : IsCompact (f₀ '' (C' ∩ f₀ ⁻¹' closedBall y r)) :=
      hE.image_of_continuousOn (hf0contB.mono (fun z hz => hC'subB hz.1))
    have hAK : f₀ '' C' ∩ closedBall y r ⊆ f₀ '' (C' ∩ f₀ ⁻¹' closedBall y r) := by
      rintro a ⟨⟨z, hzC', rfl⟩, hazK⟩
      exact ⟨z, ⟨hzC', hazK⟩, rfl⟩
    have hballK : f₀ '' C' ∩ ball y r ⊆ f₀ '' C' ∩ closedBall y r :=
      fun z hz => ⟨hz.1, Metric.ball_subset_closedBall hz.2⟩
    have hyball : y ∈ ball y r := mem_ball_self hr
    have h1 : y ∈ closure (f₀ '' C' ∩ ball y r) :=
      IsOpen.closure_inter isOpen_ball ⟨hycl, hyball⟩
    have h2 : closure (f₀ '' C' ∩ ball y r) ⊆ f₀ '' (C' ∩ f₀ ⁻¹' closedBall y r) :=
      (closure_mono hballK).trans
        ((closure_mono hAK).trans (hEc.isClosed.closure_subset_iff.mpr Subset.rfl))
    exact image_mono inter_subset_left (h2 h1)
  -- `C` is preconnected and `f₀ '' C'` is a nonempty clopen subset of it.
  have hsurj : C ⊆ f₀ '' C' :=
    hCpre.subset_of_closure_inter_subset hAopen
      ⟨f₀ x, hfxC, ⟨x, mem_connectedComponentIn hxV, rfl⟩⟩ hAcl
  exact ⟨hC'open, hC'conn, hC'diff, hmapsto, hsurj, hproper⟩

end Work.BasinSC.Tower
