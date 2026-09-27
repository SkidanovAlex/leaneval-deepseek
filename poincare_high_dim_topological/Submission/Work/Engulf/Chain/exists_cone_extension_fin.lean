import Mathlib
import Submission.Work.Engulf.Chain.ConeDefs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.ConeGeom
import Submission.Work.Engulf.Chain.ConeSetup
import Submission.Work.Engulf.Auxi.affineIndependent_insert
import Submission.Work.Engulf.Chain.affineMap_fix_simp
import Submission.Work.Engulf.Chain.affineMap_image_simp_insert
import Submission.Work.Engulf.Chain.simp_insert_inter_space
import Submission.Work.Engulf.Chain.simp_inter_coneBd
import Submission.Work.Engulf.Chain.boundary_insert_simp
import Submission.Work.Conn.ExtForm
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph

namespace Work.Engulf.Chain

open Set Metric

variable {N : ℕ} {M : Type*} [MetricSpace M]

theorem exists_extension_over_simp_aux (hS : Work.Engulf.SimplexBallForm) (V : Set M)
    (s : Finset (PL.E N)) (m : ℕ)
    (hsne : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → PL.E N))
    (hcard : s.card = m + 2) (hV : PL.ExtOverDisc V m)
    (h : PL.E N → M) (hcont : ContinuousOn h (⋃ v ∈ s, PL.simp (s.erase v)))
    (him : h '' (⋃ v ∈ s, PL.simp (s.erase v)) ⊆ V) :
    ∃ F : PL.E N → M, ContinuousOn F (PL.simp s) ∧
      Set.EqOn F h (⋃ v ∈ s, PL.simp (s.erase v)) ∧ F '' PL.simp s ⊆ V := by
  classical
  obtain ⟨e₀, he₀⟩ := hS s hsne hind
  have hbar : m + 1 = s.card - 1 := by omega
  let Φ : PL.E (m + 1) ≃ₗᵢ[ℝ] PL.E (s.card - 1) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hbar)
  have hΦmem : ∀ z : PL.E (m + 1), (z ∈ closedBall (0 : PL.E (m + 1)) 1 ↔
      Φ z ∈ closedBall (0 : PL.E (s.card - 1)) 1) := by
    intro z
    simp only [mem_closedBall, dist_zero_right, Φ.norm_map]
  have hΦsph : ∀ z : PL.E (m + 1), (z ∈ sphere (0 : PL.E (m + 1)) 1 ↔
      Φ z ∈ sphere (0 : PL.E (s.card - 1)) 1) := by
    intro z
    simp only [mem_sphere, dist_zero_right, Φ.norm_map]
  let φ : closedBall (0 : PL.E (m + 1)) 1 ≃ₜ closedBall (0 : PL.E (s.card - 1)) 1 :=
    Φ.toHomeomorph.subtype (fun x => by
      rw [LinearIsometryEquiv.coe_toHomeomorph]
      exact hΦmem x)
  have hφcoe : ∀ x : closedBall (0 : PL.E (m + 1)) 1, (φ x : PL.E (s.card - 1)) = Φ x :=
    fun x => rfl
  have hφsymm : ∀ y : closedBall (0 : PL.E (s.card - 1)) 1,
      (φ.symm y : PL.E (m + 1)) = Φ.symm y := fun y => rfl
  let e : (PL.simp s) ≃ₜ closedBall (0 : PL.E (m + 1)) 1 := e₀.trans φ.symm
  have he : ∀ x : (PL.simp s), ((e x : PL.E (m + 1)) ∈ sphere (0 : PL.E (m + 1)) 1 ↔
      (x : PL.E N) ∈ ⋃ v ∈ s, PL.simp (s.erase v)) := by
    intro x
    have h1 : ((e x : PL.E (m + 1))) = Φ.symm ((e₀ x : PL.E (s.card - 1))) := by
      simp only [e, Homeomorph.trans_apply]
      exact hφsymm (e₀ x)
    rw [h1, hΦsph (Φ.symm (e₀ x : PL.E (s.card - 1))), Φ.apply_symm_apply]
    exact he₀ x
  -- the map on the sphere, with values in `V`
  have hgc : Continuous (fun y : sphere (0 : PL.E (m + 1)) 1 =>
      ((e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩ : PL.simp s) : PL.E N)) :=
    continuous_subtype_val.comp (e.symm.continuous.comp
      (Continuous.subtype_mk continuous_subtype_val (fun y => sphere_subset_closedBall y.2)))
  have hgm : ∀ y : sphere (0 : PL.E (m + 1)) 1,
      ((e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩ : PL.simp s) : PL.E N)
        ∈ (⋃ v ∈ s, PL.simp (s.erase v)) := by
    intro y
    refine (he (e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩)).mp ?_
    rw [e.apply_symm_apply]
    exact y.2
  have hcomp : Continuous (fun y : sphere (0 : PL.E (m + 1)) 1 =>
      h ((e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩ : PL.simp s) : PL.E N)) :=
    hcont.comp_continuous hgc hgm
  obtain ⟨ψ, hψ⟩ := hV (⟨fun y : sphere (0 : PL.E (m + 1)) 1 =>
      (⟨h ((e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩ : PL.simp s) : PL.E N),
        him ⟨_, hgm y, rfl⟩⟩ : V),
      hcomp.subtype_mk (fun y => him ⟨_, hgm y, rfl⟩)⟩ : C(sphere (0 : PL.E (m + 1)) 1, V))
  -- the extension
  let F : PL.E N → M := fun z =>
    if hz : z ∈ PL.simp s then (ψ (e ⟨z, hz⟩) : M) else h z
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_subtype_val.comp (ψ.continuous.comp e.continuous)).congr (fun x => ?_)
    rw [Set.domRestrict_apply]
    rw [show F (x : PL.E N) = (ψ (e ⟨(x : PL.E N), x.2⟩) : M) from dif_pos x.2]
    rfl
  · intro x hx
    have hxs : x ∈ PL.simp s := by
      obtain ⟨v, -, hxv⟩ := mem_iUnion₂.mp hx
      exact Work.Engulf.simp_mono (Finset.erase_subset v s) hxv
    have hxsph : ((e ⟨x, hxs⟩ : closedBall (0 : PL.E (m + 1)) 1) : PL.E (m + 1))
        ∈ sphere (0 : PL.E (m + 1)) 1 := (he ⟨x, hxs⟩).mpr hx
    have hFx : F x = (ψ (e ⟨x, hxs⟩) : M) := by
      simp only [F, dif_pos hxs]
    rw [hFx]
    set y : sphere (0 : PL.E (m + 1)) 1 :=
      ⟨((e ⟨x, hxs⟩ : closedBall (0 : PL.E (m + 1)) 1) : PL.E (m + 1)), hxsph⟩ with hydef
    have hsub : (⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩
        : closedBall (0 : PL.E (m + 1)) 1) = e ⟨x, hxs⟩ := Subtype.ext rfl
    rw [show (ψ (e ⟨x, hxs⟩) : M) =
      (ψ (⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩
        : closedBall (0 : PL.E (m + 1)) 1) : M) from by rw [hsub], hψ y]
    show h ((e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩ : PL.simp s) : PL.E N) = h x
    congr 1
    have h2 : (e.symm ⟨(y : PL.E (m + 1)), sphere_subset_closedBall y.2⟩ : PL.simp s)
        = ⟨x, hxs⟩ := by
      rw [hsub, e.symm_apply_apply]
    exact congrArg Subtype.val h2
  · rintro y ⟨x, hx, rfl⟩
    simp only [F, dif_pos hx]
    exact (ψ (e ⟨x, hx⟩)).2


/-! ## Elementary topology of the cone `aσ` -/

/-- The lateral boundary `coneBd a σ` of the cone `aσ` is contained in the cone. -/
theorem coneBd_subset_simp_insert (a : PL.E N) (σ : Finset (PL.E N)) :
    coneBd a σ ⊆ PL.simp (insert a σ) := by
  intro x hx
  obtain ⟨w, _, hxw⟩ := mem_iUnion₂.mp hx
  exact Work.Engulf.simp_mono (Finset.erase_subset w (insert a σ)) hxw

/-- The boundary `⋃ v ∈ σ, simp (σ \ {v})` of a face of `Γ` is contained in `Γ.space`. -/
theorem iUnion_simp_erase_subset_space {Γ : PL.Cx N} {σ : Finset (PL.E N)} (hσ : σ ∈ Γ.faces) :
    (⋃ v ∈ σ, PL.simp (σ.erase v)) ⊆ Γ.space := by
  intro x hx
  obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
  rcases erase_mem_faces_or_empty hσ v with h | h
  · exact Γ.convexHull_subset_space h hxv
  · rw [h, Work.Engulf.simp_empty] at hxv
    exact absurd hxv (notMem_empty x)

/-- `coneBd a σ` is closed: a finite union of closed simplices. -/
theorem isClosed_coneBd (a : PL.E N) (σ : Finset (PL.E N)) : IsClosed (coneBd a σ) := by
  rw [coneBd]
  exact isClosed_biUnion_finset fun w _ => Work.Engulf.isClosed_simp _

/-- Pasting lemma: the function `if x ∈ s then f x else g x` is continuous on `s ∪ t` when `s`
and `t` are closed, `f` is continuous on `s`, `g` on `t` and they agree on `s ∩ t`. -/
theorem continuousOn_ite_union {f g : PL.E N → M} {s t : Set (PL.E N)}
    [DecidablePred (· ∈ s)]
    (hsc : IsClosed s) (htc : IsClosed t) (hf : ContinuousOn f s) (hg : ContinuousOn g t)
    (hfg : Set.EqOn f g (s ∩ t)) :
    ContinuousOn (fun x => if x ∈ s then f x else g x) (s ∪ t) := by
  classical
  refine (hf.congr ?_).union_of_isClosed (hg.congr ?_) hsc htc
  · intro x hx
    simp only [if_pos hx]
  · intro x hx
    by_cases hxs : x ∈ s
    · simp only [if_pos hxs]
      exact hfg ⟨hxs, hx⟩
    · simp only [if_neg hxs]

/-- **Extending `f` over the cone `aσ` (Newman §12), finite complex version**: let `Γ : PL.Cx N`
with *finitely many* faces (so `Γ.space` is compact and closed), `σ ∈ Γ.faces`, and let `a` be a
*generic* apex: `a ∉ affineSpan (σ ∪ s)` for every `s ∈ Γ.faces` (so in particular `a ∉ Γ.space`
and `PL.simp (insert a σ) ∩ Γ.space ⊆ PL.simp σ`).  Let `f` be continuous on `Γ.space` with `f`
mapping the boundary `σ̇ = ⋃_{v ∈ σ} PL.simp (σ \ {v})` of the simplex `σ` into `V`.  Let `A` be an
affine map of the ambient space fixing `σ` pointwise with `A a ∈ PL.simp σ`, `q = σ.card - 1`,
`M` `q`-connected and `V` nonempty and `(q-1)`-connected.  Then `f` extends to a continuous map
`f₁` on `Γ.space ∪ PL.simp (insert a σ)` which agrees with `f` on `Γ.space` and maps the lateral
boundary `Work.Engulf.Chain.coneBd a σ = ⋃_{w ∈ σ} PL.simp ((insert a σ) \ {w})` into `V`.

The hypothesis `hfin : Γ.faces.Finite` (equivalently `IsClosed Γ.space`, via
`Work.Engulf.isClosed_space`) is *necessary*: without it the conclusion fails for the complex whose
faces are the singletons `{0}` and `{p n}`, `p n = (2⁻ⁿ, 1/2) → (0, 1/2) =: x`, with `σ = {0}`,
`a = e₁ = (0,1)`, `A x = x₀ · e₀`, `V = univ`, `M = ℝ`, `f (p n) = (-1)ⁿ`: `f` is continuous on
the discrete set `Γ.space`, but any `f₁` would have to take both limit values `±1` at `x`, which
lies in the interior of `PL.simp (insert a σ)`.  (See `_ce_refute.lean` in the workspace root.)

Construction: (i) `A` retracts `coneBd a σ` onto `PL.simp σ` (it fixes the boundary `σ̇` pointwise),
(ii) `Work.Engulf.SimplexBallForm` (`Tools.simplexBall`) identifies `PL.simp σ` with `𝔻^q` with
boundary `↦` sphere, so `PL.ExtOverDisc V (q-1)` (transported along the homeomorphism, see
`Work.Cells.Connell.extOverDisc_of_homeomorph`) extends `f|σ̇` to a map `F : PL.simp σ → V`, hence
`g := F ∘ A` is a map `coneBd a σ → V` extending `f|σ̇`; (iii) on the boundary
`PL.simp σ ∪ coneBd a σ` of the disk `PL.simp (insert a σ) ≅ 𝔻^{q+1}` (again `simplexBall`) paste
`f` and `g` (both closed, agreeing on `σ̇`; use `ContinuousOn.union_of_isClosed`) and extend over
the disk using `PL.ExtOverDisc M q`; (iv) glue the resulting map on the disk with `f` on the closed
set `Γ.space` (they agree on `Γ.space ∩ PL.simp (insert a σ) ⊆ PL.simp σ`).  For `q = 0` (`σ` a
single vertex) the first step is empty and the extension is a path from `f v` to a point of `V` in
`M`. -/
theorem exists_cone_extension_fin {N : ℕ} {M : Type*} [MetricSpace M]
    (hS : Work.Engulf.SimplexBallForm)
    (V : Set M) (Γ : PL.Cx N) (σ : Finset (PL.E N)) (a : PL.E N) (f : PL.E N → M)
    (A : PL.E N →ᵃ[ℝ] PL.E N)
    (hfin : Γ.faces.Finite) (hσ : σ ∈ Γ.faces)
    (hgen : ∀ s ∈ Γ.faces,
      a ∉ (affineSpan ℝ (((σ ∪ s : Finset (PL.E N)) : Set (PL.E N))) : Set (PL.E N)))
    (hcont : ContinuousOn f Γ.space)
    (hbd : f '' (⋃ v ∈ σ, PL.simp (σ.erase v)) ⊆ V)
    (hA : ∀ v ∈ σ, A v = v) (hAa : A a ∈ PL.simp σ)
    (hVne : V.Nonempty)
    (hM : ∀ j, j + 2 ≤ σ.card + 1 → PL.ExtOverDisc M j)
    (hV : ∀ j, j + 2 ≤ σ.card → PL.ExtOverDisc V j) :
    ∃ f₁ : PL.E N → M, ContinuousOn f₁ (Γ.space ∪ PL.simp (insert a σ)) ∧
      Set.EqOn f₁ f Γ.space ∧ f₁ '' Work.Engulf.Chain.coneBd a σ ⊆ V := by
  classical
  -- ## Elementary consequences of the hypotheses
  have hσne : σ.Nonempty := Γ.nonempty_of_mem_faces hσ
  have hσcard : 1 ≤ σ.card := Finset.card_pos.mpr hσne
  have hind : AffineIndependent ℝ ((↑) : σ → PL.E N) := Γ.indep hσ
  -- the apex lies outside the affine span of `σ` (genericity at `s = σ`)
  have ha_span : a ∉ (affineSpan ℝ ((σ : Set (PL.E N))) : Set (PL.E N)) := by
    have h := hgen σ hσ
    rwa [Finset.union_self] at h
  have haσ : a ∉ σ := fun h =>
    ha_span (subset_affineSpan ℝ ((σ : Set (PL.E N))) (by simpa using h))
  -- ## Step 1: extend `f` from the boundary of `σ` over all of `PL.simp σ`, with values in `V`
  have hF_ex : ∃ F : PL.E N → M, ContinuousOn F (PL.simp σ) ∧
      Set.EqOn F f (⋃ v ∈ σ, PL.simp (σ.erase v)) ∧ F '' PL.simp σ ⊆ V := by
    rcases lt_or_ge σ.card 2 with hlt | hge
    · -- `σ` is a single vertex: its boundary is empty and any point of `V` works
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by omega : σ.card = 1)
      obtain ⟨v₀, hv₀⟩ := hVne
      refine ⟨fun _ => v₀, continuousOn_const, ?_, ?_⟩
      · intro x hx
        obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
        have hwv : w = v := by simpa using hw
        have hzero : ({v} : Finset (PL.E N)).erase w = ∅ := by
          rw [Finset.erase_eq_empty_iff]
          exact Or.inr (by simp only [hwv])
        rw [hzero, Work.Engulf.simp_empty] at hxw
        exact absurd hxw (notMem_empty x)
      · rintro y ⟨z, -, rfl⟩
        exact hv₀
    · -- `σ` has at least two vertices: use the disk step
      have hcard : σ.card = (σ.card - 2) + 2 := by omega
      exact exists_extension_over_simp_aux hS V σ (σ.card - 2) hσne hind hcard
        (hV (σ.card - 2) (by omega)) f (hcont.mono (iUnion_simp_erase_subset_space hσ)) hbd
  obtain ⟨F, hFc, hFf, hFV⟩ := hF_ex
  -- ## Step 2: the retraction `A` pushes the lateral boundary into `PL.simp σ`
  have hAfix : ∀ x ∈ PL.simp σ, A x = x := affineMap_fix_simp A hA
  have hAmap : A '' PL.simp (insert a σ) ⊆ PL.simp σ := affineMap_image_simp_insert A hA hAa
  set g : PL.E N → M := fun x => F (A x) with hgdef
  have hconeBd_sub : coneBd a σ ⊆ PL.simp (insert a σ) := coneBd_subset_simp_insert a σ
  have hgA : ∀ x ∈ coneBd a σ, A x ∈ PL.simp σ :=
    fun x hx => hAmap ⟨x, hconeBd_sub hx, rfl⟩
  have hgc : ContinuousOn g (coneBd a σ) :=
    (hFc.comp A.continuous_of_finiteDimensional.continuousOn hgA).congr
      (fun x _ => by simp only [hgdef, Function.comp_apply])
  have hgV : g '' coneBd a σ ⊆ V := by
    rintro y ⟨x, hx, rfl⟩
    exact hFV ⟨A x, hgA x hx, rfl⟩
  -- `f` and `g` agree on the boundary of `σ` (where `A` is the identity)
  have hfg : Set.EqOn f g (⋃ v ∈ σ, PL.simp (σ.erase v)) := by
    intro x hx
    have hxs : x ∈ PL.simp σ := by
      obtain ⟨v, _, hxv⟩ := mem_iUnion₂.mp hx
      exact Work.Engulf.simp_mono (Finset.erase_subset v σ) hxv
    simp only [hgdef]
    rw [hAfix x hxs]
    exact (hFf hx).symm
  -- ## Step 3: paste `f` (on `PL.simp σ`) and `g` (on `coneBd a σ`) on the boundary of the disk
  set bdy : PL.E N → M := fun x => if x ∈ PL.simp σ then f x else g x with hbdydef
  have hbd_eq : (⋃ v ∈ insert a σ, PL.simp ((insert a σ).erase v)) = PL.simp σ ∪ coneBd a σ :=
    boundary_insert_simp σ a haσ
  have hbdy_simp : Set.EqOn bdy f (PL.simp σ) := by
    intro x hx
    simp only [hbdydef, if_pos hx]
  have hbdy_coneBd : Set.EqOn bdy g (coneBd a σ) := by
    intro x hx
    by_cases hxσ : x ∈ PL.simp σ
    · have hxbd : x ∈ (⋃ v ∈ σ, PL.simp (σ.erase v)) :=
        simp_inter_coneBd Γ σ a hσ hgen ⟨hxσ, hx⟩
      simp only [hbdydef, if_pos hxσ]
      exact hfg hxbd
    · simp only [hbdydef, if_neg hxσ]
  have hbdy_c : ContinuousOn bdy (PL.simp σ ∪ coneBd a σ) := by
    have h := continuousOn_ite_union (f := f) (g := g) (s := PL.simp σ) (t := coneBd a σ)
      (Work.Engulf.isClosed_simp σ) (isClosed_coneBd a σ)
      (hcont.mono (Γ.convexHull_subset_space hσ)) hgc
      (fun x hx => hfg (simp_inter_coneBd Γ σ a hσ hgen hx))
    exact h.congr (fun x _ => by simp only [hbdydef])
  have hbdy_c' : ContinuousOn bdy (⋃ v ∈ insert a σ, PL.simp ((insert a σ).erase v)) := by
    rw [hbd_eq]
    exact hbdy_c
  -- ## Step 4: extend `bdy` over the disk `PL.simp (insert a σ)`
  have hcard_insert : (insert a σ).card = (σ.card - 1) + 2 := by
    rw [Finset.card_insert_of_notMem haσ]
    omega
  have hind_insert :
      AffineIndependent ℝ (fun v : (insert a σ : Finset (PL.E N)) => (v : PL.E N)) :=
    Work.Engulf.Aux.affineIndependent_insert hind ha_span
  have hVuniv : PL.ExtOverDisc (Set.univ : Set M) (σ.card - 1) :=
    Work.Cells.Connell.extOverDisc_of_homeomorph (Homeomorph.Set.univ M).symm
      (hM (σ.card - 1) (by omega))
  obtain ⟨Fd, hFdc, hFdf, _⟩ :=
    exists_extension_over_simp_aux hS (Set.univ : Set M) (insert a σ) (σ.card - 1)
      (Finset.insert_nonempty a σ) hind_insert hcard_insert hVuniv bdy hbdy_c'
      (fun y _ => Set.mem_univ y)
  -- ## Step 5: glue the disk map with `f` on the closed set `Γ.space`
  have hInter : PL.simp (insert a σ) ∩ Γ.space ⊆ PL.simp σ :=
    simp_insert_inter_space Γ σ a hσ hgen
  have hEqΓ : Set.EqOn (fun x => if x ∈ PL.simp (insert a σ) then Fd x else f x) f Γ.space := by
    intro x hx
    by_cases hxB : x ∈ PL.simp (insert a σ)
    · have hxσ : x ∈ PL.simp σ := hInter ⟨hxB, hx⟩
      have hxu : x ∈ (⋃ v ∈ insert a σ, PL.simp ((insert a σ).erase v)) := by
        rw [hbd_eq]
        exact Or.inl hxσ
      simp only [if_pos hxB, hFdf hxu, hbdy_simp hxσ]
    · simp only [if_neg hxB]
  have hcEm : ContinuousOn (fun x => if x ∈ PL.simp (insert a σ) then Fd x else f x)
      Γ.space :=
    hcont.congr hEqΓ
  have hcB : ContinuousOn (fun x => if x ∈ PL.simp (insert a σ) then Fd x else f x)
      (PL.simp (insert a σ)) :=
    hFdc.congr (fun x hx => by simp only [if_pos hx])
  refine ⟨fun x => if x ∈ PL.simp (insert a σ) then Fd x else f x, ?_, hEqΓ, ?_⟩
  · exact hcEm.union_of_isClosed hcB (Work.Engulf.isClosed_space hfin) (Work.Engulf.isClosed_simp _)
  · rintro y ⟨x, hx, rfl⟩
    have hxB : x ∈ PL.simp (insert a σ) := hconeBd_sub hx
    have hxu : x ∈ (⋃ v ∈ insert a σ, PL.simp ((insert a σ).erase v)) := by
      rw [hbd_eq]
      exact Or.inr hx
    simp only [if_pos hxB, hFdf hxu, hbdy_coneBd hx]
    exact hgV ⟨x, hx, rfl⟩


end Work.Engulf.Chain
