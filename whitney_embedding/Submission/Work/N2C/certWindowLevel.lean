import Mathlib
import Submission.Work.N2C.extremumWindowCertAux
import Submission.Work.N2C.isCertifiedAt_of_roundImage
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2.exists_levelComponentCurves
import Submission.Work.Drive.N2.extremumLanding

/-!
# The certificate at one level of the extremum window

This file produces the two certificates of the certified extremum window
(`Work.N2C.exists_certifiedWindow_extremum`).  The drawing is the hybrid

    `W x = if x ∈ Dm then extremumCollapse φ μ x else A₀ (foot x)`

of `Work.N2C.Ext.extremumWindowExposed_picture`, and the certificate at a band level `u` is obtained
from `Work.N2C.isCertifiedAt_of_roundImage`: it suffices to exhibit, for a parametrisation `L` of the
level `u`, circles `c i + r i • roundPic (·)` through the pictures `W (L.γ i x)` of its curves, with
pairwise disjoint circles.

The pictures are read off the two pieces of the hybrid:

* the **model piece**: on `Dm` the picture is the radial collapse, whose image on the level is the
  circle of radius `μ (r²) · r` around `0` (`r` the chart radius of the level);
* the **transport piece**: off `Dm` the picture is `A₀ ∘ foot`, and the landing row puts `foot x` on
  the anchor level, where `A₀` reads a round configuration through the anchor parametrisation.
-/

namespace Work.N2C

open scoped Manifold ContDiff Topology
open Set Filter

namespace Ext

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The circle of a configuration, as a combination of the two angle functions. -/
lemma circle_eq_ang_combo' {m : ℕ} (D : Work.Drive.N2.RoundConfig m) (j : Fin m) (t : ℝ) :
    D.circle j t = D.pos j + D.rad j •
      (Real.cos (D.phase j) • Work.Drive.N2.ang t +
        Real.sin (D.phase j) • Work.Drive.N2.angPerp t) :=
  Work.Drive.N2.circle_eq_ang_combo D j t

lemma contDiff_circle {m : ℕ} (D : Work.Drive.N2.RoundConfig m) (j : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (D.circle j) := by
  have h : D.circle j = fun t : ℝ => D.pos j + D.rad j •
      (Real.cos (D.phase j) • Work.Drive.N2.ang t +
        Real.sin (D.phase j) • Work.Drive.N2.angPerp t) :=
    funext fun t => circle_eq_ang_combo' D j t
  rw [h]
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.cos (D.phase j) • Work.Drive.N2.ang t) :=
    (contDiff_const (c := Real.cos (D.phase j))).smul Work.Drive.N2.ang_contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.sin (D.phase j) • Work.Drive.N2.angPerp t) :=
    (contDiff_const (c := Real.sin (D.phase j))).smul Work.Drive.N2.angPerp_contDiff
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.cos (D.phase j) • Work.Drive.N2.ang t +
        Real.sin (D.phase j) • Work.Drive.N2.angPerp t) := h1.add h2
  exact (contDiff_const (c := D.pos j)).add ((contDiff_const (c := D.rad j)).smul h3)

lemma circle_period {m : ℕ} (D : Work.Drive.N2.RoundConfig m) (j : Fin m) (x : ℝ) :
    D.circle j (x + 1) = D.circle j x := by
  rw [circle_eq_ang_combo' D j (x + 1), circle_eq_ang_combo' D j x,
    Work.Drive.N2.ang_periodic x, Work.Drive.N2.angPerp_periodic x]

/-- **The circle of a round configuration is compact** (it is the image of `[0,1]`). -/
lemma isCompact_range_circle {m : ℕ} (D : Work.Drive.N2.RoundConfig m) (j : Fin m) :
    IsCompact (Set.range (D.circle j)) := by
  have hrange : Set.range (D.circle j) = D.circle j '' Set.Icc 0 1 := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨Int.fract t, ⟨Int.fract_nonneg t, le_of_lt (Int.fract_lt_one t)⟩, ?_⟩
      exact (Work.Drive.N2C.eq_fract_of_periodic (circle_period D j) t).symm
    · rintro ⟨s, _, rfl⟩
      exact ⟨s, rfl⟩
  rw [hrange]
  exact isCompact_Icc.image (contDiff_circle D j).continuous

lemma isClosed_range_circle {m : ℕ} (D : Work.Drive.N2.RoundConfig m) (j : Fin m) :
    IsClosed (Set.range (D.circle j)) :=
  (isCompact_range_circle D j).isClosed

/-- Points of the range of a circle of a configuration. -/
lemma mem_range_circle_iff {m : ℕ} (D : Work.Drive.N2.RoundConfig m) (j : Fin m) (y : E3) :
    y ∈ Set.range (D.circle j) ↔ ∃ t : ℝ, y = D.pos j + D.rad j • Work.Drive.N2.roundPic
      (D.phase j + 2 * Real.pi * t) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl⟩

/-- **`IsLevelIsotopy` from the three rows of a good drawing.**  If `W` is smooth on the level
`f = u`, injective on it and immersive on `ker (df)` there, then the constant family `s ↦ W` is a
level isotopy. -/
theorem isLevelIsotopy_const_of_rows {f : M → ℝ} {u : ℝ} {W : M → E3}
    (hWsm : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) W y)
    (hWinj : ∀ x y : M, f x = u → f y = u → W x = W y → x = y)
    (hWimm : ∀ x : M, f x = u → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) W x v = 0 → v = 0) :
    Work.Drive.N2C.IsLevelIsotopy f u (fun _ : ℝ => W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s y hy
    have h := hWsm y hy
    have h2 : (fun p : ℝ × M => W p.2) = W ∘ Prod.snd := rfl
    rw [h2]
    exact h.comp (s, y) contMDiffAt_snd
  · intro s x y hx hy hxy
    exact hWinj x y hx hy hxy
  · intro s y hy v hv hv'
    exact hWimm y hy v hv hv'

/-! ## The round picture data at one level -/

/-- **The circles through the pictures of one level of the hybrid.**

`W` is the hybrid model/transport drawing, `γu` a parametrisation of the level `u`.  Every component
of the level is drawn as a round circle: either the component lies in the model ball, where the
picture is the radial collapse (its image on the level `u` is the circle of radius `μ r² · r`, `r` the
chart radius of the level), or it lies outside, where the picture is the anchor picture composed with
the transport map and the anchor level reads a round configuration there. -/
theorem exists_roundData_of_hybrid {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {u a c s b : ℝ} (hu_ne : u ≠ c) (hs : s = 1 ∨ s = -1)
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hmodel : ∀ y ∈ φ.source, f y = c + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2))
    (hDmopen : IsOpen (Work.Drive.N2.modelBall φ b))
    (hDmclosed : IsClosed (Work.Drive.N2.modelBall φ b ∩ {x : M | f x = u}))
    {μ : ℝ → ℝ} (hμpos : ∀ t, 0 < μ t)
    {W A₀ : M → E3} {foot : M → M}
    (hA₀sm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A₀ y)
    (hfootsm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot y)
    (hWu : ∀ y : M, f y = u →
      W y = Ext.hybridW φ μ b A₀ foot y)
    {na : ℕ} {γa : Fin na → ℝ → M} {Da : Work.Drive.N2.RoundConfig na}
    (hDacover : ∀ y : M, f y = a → ∃ (i : Fin na) (t : ℝ), y = γa i t)
    (hAcirc : ∀ (i : Fin na) (x : ℝ), A₀ (γa i x) = Da.circle i x)
    (hDaD : Da.Disjoint)
    (hland : ∀ x : M, x ∉ Work.Drive.N2.modelBall φ b → f x = u → f (foot x) = a)
    {nu : ℕ} {γu : Fin nu → ℝ → M}
    (hγsm : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (γu i))
    (hγval : ∀ (i : Fin nu) (x : ℝ), f (γu i x) = u) :
    ∃ (c' : Fin nu → E3) (r' : Fin nu → ℝ), (∀ i, 0 < r' i) ∧
      (∀ (i : Fin nu) (x : ℝ), ∃ t : ℝ, W (γu i x) = c' i + r' i • Work.Drive.N2.roundPic t) := by
  classical
  have hKey : ∀ i : Fin nu, ∃ (c' : E3) (r' : ℝ), 0 < r' ∧
      (∀ x : ℝ, ∃ t : ℝ, W (γu i x) = c' + r' • Work.Drive.N2.roundPic t) := by
    intro i
    have hγcont : Continuous (γu i) := (hγsm i).continuous
    have hin : ∀ x : ℝ, f (γu i x) = u := fun x => hγval i x
    have hSclosed : IsClosed {x : ℝ | γu i x ∈ Work.Drive.N2.modelBall φ b} := by
      have h : {x : ℝ | γu i x ∈ Work.Drive.N2.modelBall φ b} =
          (γu i) ⁻¹' (Work.Drive.N2.modelBall φ b ∩ {x : M | f x = u}) := by
        ext x
        constructor
        · intro hx; exact ⟨hx, hin x⟩
        · intro hx; exact hx.1
      rw [h]
      exact hDmclosed.preimage hγcont
    have hSopen : IsOpen {x : ℝ | γu i x ∈ Work.Drive.N2.modelBall φ b} :=
      hDmopen.preimage hγcont
    by_cases hmem : γu i 0 ∈ Work.Drive.N2.modelBall φ b
    · -- the component lies in the model ball
      have hall : ∀ x : ℝ, γu i x ∈ Work.Drive.N2.modelBall φ b := by
        have hsub : (Set.univ : Set ℝ) ⊆
            {x : ℝ | γu i x ∈ Work.Drive.N2.modelBall φ b} :=
          IsPreconnected.subset_left_of_subset_union hSopen hSclosed.isOpen_compl
            disjoint_compl_right
            (by intro x _; by_cases h : γu i x ∈ Work.Drive.N2.modelBall φ b <;> simp [h])
            ⟨0, ⟨Set.mem_univ 0, hmem⟩⟩ isPreconnected_univ
        exact fun x => hsub (Set.mem_univ x)
      have hsval : ∀ x : ℝ, s * ‖φ (γu i x)‖ ^ 2 = u - c := by
        intro x
        have hy := hall x
        have h1 : f (γu i x) = c + s * ((φ (γu i x)) 0 ^ 2 + (φ (γu i x)) 1 ^ 2) :=
          hmodel _ hy.1
        have h2 := Work.Drive.N2.coord_sq_eq_norm_sq (φ (γu i x))
        rw [h2] at h1
        rw [hin x] at h1
        linarith
      have hnorm : ∀ x : ℝ, ‖φ (γu i x)‖ = ‖φ (γu i 0)‖ := by
        intro x
        have ha := hsval x
        have hb := hsval 0
        have h4 : ‖φ (γu i x)‖ ^ 2 = ‖φ (γu i 0)‖ ^ 2 := by
          rcases hs with h | h <;> rw [h] at ha hb <;> nlinarith
        nlinarith [norm_nonneg (φ (γu i x)), norm_nonneg (φ (γu i 0))]
      have hne : ‖φ (γu i 0)‖ ≠ 0 := by
        intro h0
        have hb := hsval 0
        rw [h0] at hb
        have huc : u - c = 0 := by
          rcases hs with h | h <;> rw [h] at hb <;> linarith [hb]
        exact hu_ne (by linarith)
      have hpos : 0 < ‖φ (γu i 0)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      refine ⟨0, μ (‖φ (γu i 0)‖ ^ 2) * ‖φ (γu i 0)‖, mul_pos (hμpos _) hpos, ?_⟩
      intro x
      obtain ⟨t, ht⟩ := Ext.exists_roundPic_of_incl23 (φ (γu i x))
      refine ⟨t, ?_⟩
      rw [hWu (γu i x) (hin x), Ext.hybridW, if_pos (hall x)]
      rw [Work.Drive.N2.extremumCollapse, map_smul, ht, ← hnorm x, smul_smul, zero_add]
    · -- the component lies outside the model ball
      have hall : ∀ x : ℝ, γu i x ∉ Work.Drive.N2.modelBall φ b := by
        have hsub : (Set.univ : Set ℝ) ⊆
            {x : ℝ | γu i x ∈ Work.Drive.N2.modelBall φ b}ᶜ :=
          IsPreconnected.subset_left_of_subset_union hSclosed.isOpen_compl hSopen
            disjoint_compl_left
            (by intro x _; by_cases h : γu i x ∈ Work.Drive.N2.modelBall φ b <;> simp [h])
            ⟨0, ⟨Set.mem_univ 0, hmem⟩⟩ isPreconnected_univ
        exact fun x => hsub (Set.mem_univ x)
      have hAF : Continuous (fun y : M => A₀ (foot y)) :=
        continuous_iff_continuousAt.mpr fun y =>
          ((hA₀sm (foot y)).continuousAt).comp ((hfootsm y).continuousAt)
      have hAfootcont : Continuous (fun x : ℝ => A₀ (foot (γu i x))) :=
        hAF.comp hγcont
      have hlandx : ∀ x : ℝ, f (foot (γu i x)) = a :=
        fun x => hland (γu i x) (hall x) (hin x)
      set T : Fin na → Set ℝ := fun j => {x : ℝ | A₀ (foot (γu i x)) ∈ Set.range (Da.circle j)}
        with hTdef
      have hTclosed : ∀ j : Fin na, IsClosed (T j) :=
        fun j => (Ext.isClosed_range_circle Da j).preimage hAfootcont
      have hTcov : ∀ x : ℝ, ∃ j : Fin na, x ∈ T j := by
        intro x
        obtain ⟨j, t, ht⟩ := hDacover (foot (γu i x)) (hlandx x)
        exact ⟨j, by rw [hTdef]; exact ⟨t, by rw [ht, hAcirc]⟩⟩
      have hTdisj : ∀ x : ℝ, ∀ j j' : Fin na, x ∈ T j → x ∈ T j' → j = j' := by
        intro x j j' hj hj'
        by_contra hne
        rw [hTdef] at hj hj'
        obtain ⟨t, ht⟩ := hj
        obtain ⟨t', ht'⟩ := hj'
        exact hDaD j j' hne t t' (ht.trans ht'.symm)
      obtain ⟨j₀, hj₀⟩ := hTcov 0
      have hTopen : IsOpen (T j₀) := by
        have hcompl : (T j₀)ᶜ = ⋃ (j : {j : Fin na // j ≠ j₀}), T j.val := by
          ext y
          constructor
          · intro hy
            obtain ⟨j, hj⟩ := hTcov y
            exact Set.mem_iUnion.mpr ⟨⟨j, fun h => hy (h ▸ hj)⟩, hj⟩
          · intro hy hy'
            obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
            exact j.prop (hTdisj y j.val j₀ hj hy')
        have hc : IsClosed (T j₀)ᶜ := by
          rw [hcompl]
          exact isClosed_iUnion_of_finite fun j => hTclosed j.val
        exact isClosed_compl_iff.mp hc
      have hallj : ∀ x : ℝ, x ∈ T j₀ := by
        have hsub : (Set.univ : Set ℝ) ⊆ T j₀ :=
          IsPreconnected.subset_left_of_subset_union hTopen (hTclosed j₀).isOpen_compl
            disjoint_compl_right
            (by intro x _; by_cases h : x ∈ T j₀ <;> simp [h])
            ⟨0, ⟨Set.mem_univ 0, hj₀⟩⟩ isPreconnected_univ
        exact fun x => hsub (Set.mem_univ x)
      refine ⟨Da.pos j₀, Da.rad j₀, Da.hrad j₀, ?_⟩
      intro x
      have hxT : x ∈ T j₀ := hallj x
      rw [hTdef] at hxT
      obtain ⟨t, ht⟩ := hxT
      refine ⟨Da.phase j₀ + 2 * Real.pi * t, ?_⟩
      rw [hWu (γu i x) (hin x), Ext.hybridW, if_neg (hall x), ← ht]
      rfl
  choose c' r' hspec using hKey
  exact ⟨c', r', fun i => (hspec i).1, fun i x => (hspec i).2 x⟩

/-! ## Disjointness of the circles -/

/-- **The circles through the pictures of the components of a level are pairwise disjoint.**

Each circle is traversed by the picture of one component curve (by the reparametrisation
`Work.N2C.exists_reparam_level`), and distinct components have disjoint ranges, so two distinct
circles cannot meet. -/
theorem roundData_disjoint {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {u : ℝ} (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {e : ℝ → M → E3} (he : Work.Drive.N2C.IsLevelIsotopy f u e)
    {n : ℕ} (L : Work.Drive.N2C.LevelCurves f u n) {c' : Fin n → E3} {r' : Fin n → ℝ}
    (hr : ∀ i, 0 < r' i)
    (hround : ∀ (i : Fin n) (x : ℝ), ∃ t : ℝ,
      e 1 (L.γ i x) = c' i + r' i • Work.Drive.N2.roundPic t)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (L.γ i)) (Set.range (L.γ j))) :
    ∀ i j : Fin n, i ≠ j → ∀ t t' : ℝ,
      c' i + r' i • Work.Drive.N2.roundPic t ≠ c' j + r' j • Work.Drive.N2.roundPic t' := by
  intro i j hij t t' h
  obtain ⟨τ, φ, ε, hτ, hε, hsh, hsurj, hmono, hder, hid⟩ :=
    Work.N2C.exists_reparam_level hf hreg he L c' r' hr hround i
  obtain ⟨τ', φ', ε', hτ', hε', hsh', hsurj', hmono', hder', hid'⟩ :=
    Work.N2C.exists_reparam_level hf hreg he L c' r' hr hround j
  have harg : φ + 2 * Real.pi * ((t - φ) / (2 * Real.pi)) = t := by
    field_simp
    ring
  have harg' : φ' + 2 * Real.pi * ((t' - φ') / (2 * Real.pi)) = t' := by
    field_simp
    ring
  have e1 : c' i + r' i • Work.Drive.N2.roundPic t =
      e 1 (L.γ i (τ ((t - φ) / (2 * Real.pi)))) := by
    have h1 := hid ((t - φ) / (2 * Real.pi))
    rw [harg] at h1
    exact h1.symm
  have e2 : c' j + r' j • Work.Drive.N2.roundPic t' =
      e 1 (L.γ j (τ' ((t' - φ') / (2 * Real.pi)))) := by
    have h2 := hid' ((t' - φ') / (2 * Real.pi))
    rw [harg'] at h2
    exact h2.symm
  rw [e1, e2] at h
  have hγ : L.γ i (τ ((t - φ) / (2 * Real.pi))) = L.γ j (τ' ((t' - φ') / (2 * Real.pi))) :=
    he.2.1 1 _ _ (L.val i _) (L.val j _) h
  exact Set.disjoint_left.mp (hdisj i j hij) ⟨_, rfl⟩ ⟨_, hγ.symm⟩

/-! ## The certificate at one level -/

/-- **The certificate of the hybrid drawing at a level of its window.** -/
theorem isCertifiedAt_of_hybrid {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {u a c s b : ℝ} (hu_ne : u ≠ c) (hs : s = 1 ∨ s = -1)
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    (hmodel : ∀ y ∈ φ.source, f y = c + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2))
    (hDmopen : IsOpen (Work.Drive.N2.modelBall φ b))
    (hDmclosed : IsClosed (Work.Drive.N2.modelBall φ b ∩ {x : M | f x = u}))
    {μ : ℝ → ℝ} (hμpos : ∀ t, 0 < μ t)
    {W A₀ : M → E3} {foot : M → M}
    (hA₀sm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A₀ y)
    (hfootsm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot y)
    (hWu : ∀ y : M, f y = u → W y = Ext.hybridW φ μ b A₀ foot y)
    {na : ℕ} {γa : Fin na → ℝ → M} {Da : Work.Drive.N2.RoundConfig na}
    (hDacover : ∀ y : M, f y = a → ∃ (i : Fin na) (t : ℝ), y = γa i t)
    (hAcirc : ∀ (i : Fin na) (x : ℝ), A₀ (γa i x) = Da.circle i x)
    (hDaD : Da.Disjoint)
    (hland : ∀ x : M, x ∉ Work.Drive.N2.modelBall φ b → f x = u → f (foot x) = a)
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    (hWsm : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) W y)
    (hWinj : ∀ x y : M, f x = u → f y = u → W x = W y → x = y)
    (hWimm : ∀ x : M, f x = u → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) W x v = 0 → v = 0) :
    Work.Drive.N2C.IsCertifiedAt f u W := by
  classical
  by_cases hne : ∃ x : M, f x = u
  · obtain ⟨nu, γu, hγsm, hγper, hγinj, hγval, hγderiv, hγker, hγcovU, hγdisj, hγclosed,
      hγmod⟩ := Work.Drive.N2.exists_levelComponentCurves f hf u hreg hne
    have hcover : ∀ x : M, f x = u → ∃ (i : Fin nu) (t : ℝ), x = γu i t := by
      intro x hx
      have h : x ∈ ⋃ i, Set.range (γu i) := by rw [hγcovU]; exact hx
      simp only [Set.mem_iUnion, Set.mem_range] at h
      obtain ⟨i, t, ht⟩ := h
      exact ⟨i, t, ht.symm⟩
    let L : Work.Drive.N2C.LevelCurves f u nu :=
      { γ := γu, sm := hγsm, val := hγval, per := hγper, injIco := hγinj,
        modOne := fun i => Work.Drive.N2C.exists_int_sub_of_periodic_injOn (hγper i) (hγinj i),
        cover := hcover, disj := hγdisj, ker := hγker }
    obtain ⟨c', r', hr, hroundW⟩ :=
      Ext.exists_roundData_of_hybrid (f := f) hf (a := a) (c := c) (s := s) (b := b) hu_ne hs
        hmodel hDmopen hDmclosed hμpos hA₀sm hfootsm hWu hDacover hAcirc hDaD hland hγsm hγval
    have he : Work.Drive.N2C.IsLevelIsotopy f u (fun _ : ℝ => W) :=
      Ext.isLevelIsotopy_const_of_rows hWsm hWinj hWimm
    have hround : ∀ (i : Fin nu) (x : ℝ), ∃ t : ℝ,
        (fun _ : ℝ => W) 1 (L.γ i x) = c' i + r' i • Work.Drive.N2.roundPic t := by
      intro i x
      obtain ⟨t, ht⟩ := hroundW i x
      exact ⟨t, ht⟩
    have hdisj : ∀ i j : Fin nu, i ≠ j → Disjoint (Set.range (L.γ i)) (Set.range (L.γ j)) :=
      hγdisj
    have hsep := Ext.roundData_disjoint (f := f) hf hreg he L hr hround hdisj
    exact Work.N2C.isCertifiedAt_of_roundImage hf hreg he (fun y _ => rfl) L c' r' hr hround hsep
  · exact Work.Drive.N2C.isCertifiedAt_of_empty (f := f) (u := u) (g := W)
      (fun y hy => hne ⟨y, hy⟩)

end Ext

end Work.N2C
