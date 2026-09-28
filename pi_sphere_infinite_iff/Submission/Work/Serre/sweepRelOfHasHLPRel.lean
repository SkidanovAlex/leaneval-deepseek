import Mathlib
import Submission.Work.Serre.SweepRelDefs

/-!
# The disk step `SweepRel m` from the relative homotopy lifting property

`Work.Serre.SweepRel m p` (`Submission/Work/Serre/SweepRelDefs.lean`) is the "three faces"
lifting property `Work.Serre.Sweep` for the cube `I^m`, with the lateral boundary
`∂I^m × I × I` also prescribed.  This file proves that it follows from the relative homotopy
lifting property `Work.StemsB.HasHLPRel p (m+1)` for the pair
`(I^{m+1} × {0} ∪ ∂I^{m+1} × I) ⊂ I^{m+1} × I`, i.e. from the HLP of `p` for the prism
`I^{m+1} × I` whose lift is prescribed on the "cup" `I^{m+1} × {0} ∪ ∂I^{m+1} × I`.

The proof identifies `I^{m+1} ≅ I^m × I` (`initPt` / `snocPt`) so that

* the cube coordinate is `(z,t) ∈ I^m × I`,
* the homotopy coordinate is `s ∈ I`,

the initial lift is `(z,t) ↦ f₀ (z,t)`, and the boundary lift on `∂(I^m × I) × I` is glued from
`Grim` (on `∂I^m × I`), `f₁` (on `t = 0`) and `f₂` (on `t = 1`).  The glueing is the pasting
lemma for the closed cover `{∂I^m × I, t = 0, t = 1}` of `∂(I^m × I)`, and is carried out in
`boundaryLiftAux` below (together with the two properties the HLP consumes).
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B] {m : ℕ}

/-! ## Continuity of the coordinate identifications `I^{m+1} ≅ I^m × I` -/

theorem continuous_initPt_local :
    Continuous (initPt : (Fin (m + 1) → unitInterval) → (Fin m → unitInterval)) :=
  continuous_pi fun i => (continuous_apply i.castSucc : _)

/-! ## The boundary lift

Given the data of `SweepRel`, the boundary of `∂(I^m × I) × I ≅ ∂I^{m+1} × I` is covered by the
three closed pieces `{∂I^m × I}`, `{t = 0}`, `{t = 1}`, on which the lift is prescribed by
`Grim`, `f₁`, `f₂` respectively.  The three prescriptions agree on the overlaps, so they glue to a
continuous lift `g` of `H` on the whole boundary; this `g` is the boundary datum of the relative
homotopy lifting property `HasHLPRel p (m+1)`. -/

theorem boundaryLiftAux (p : C(E, B))
    (H : C((Fin m → unitInterval) × unitInterval × unitInterval, B))
    (f₀ f₁ f₂ : C((Fin m → unitInterval) × unitInterval, E))
    (Grim : C(Work.StemsB.CubeBdry m × unitInterval × unitInterval, E))
    (hGrim : ∀ (x : Work.StemsB.CubeBdry m) (a b : unitInterval),
      p (Grim (x, a, b)) = H (x.1, a, b))
    (hGrim₀ : ∀ (x : Work.StemsB.CubeBdry m) (b : unitInterval), Grim (x, 0, b) = f₀ (x.1, b))
    (hGrim₁ : ∀ (x : Work.StemsB.CubeBdry m) (a : unitInterval), Grim (x, a, 0) = f₁ (x.1, a))
    (hGrim₂ : ∀ (x : Work.StemsB.CubeBdry m) (a : unitInterval), Grim (x, a, 1) = f₂ (x.1, a))
    (h₁ : ∀ (x : Fin m → unitInterval) (a : unitInterval), p (f₁ (x, a)) = H (x, a, 0))
    (h₂ : ∀ (x : Fin m → unitInterval) (a : unitInterval), p (f₂ (x, a)) = H (x, a, 1))
    (c₀ : ∀ x : Fin m → unitInterval, f₀ (x, 0) = f₁ (x, 0))
    (c₁ : ∀ x : Fin m → unitInterval, f₀ (x, 1) = f₂ (x, 0)) :
    ∃ g : C(Work.StemsB.CubeBdry (m + 1) × unitInterval, E),
      (∀ (y : Work.StemsB.CubeBdry (m + 1)) (s : unitInterval),
        p (g (y, s)) = H (initPt y.1, s, y.1 (Fin.last m))) ∧
      (∀ (y : Work.StemsB.CubeBdry (m + 1)),
        g (y, 0) = f₀ (initPt y.1, y.1 (Fin.last m))) ∧
      (∀ (y : Work.StemsB.CubeBdry (m + 1)) (s : unitInterval)
        (h : initPt y.1 ∈ Cube.boundary (Fin m)),
        g (y, s) = Grim (⟨initPt y.1, h⟩, s, y.1 (Fin.last m))) ∧
      (∀ (y : Work.StemsB.CubeBdry (m + 1)) (s : unitInterval)
        (h : y.1 (Fin.last m) = 0),
        g (y, s) = f₁ (initPt y.1, s)) ∧
      (∀ (y : Work.StemsB.CubeBdry (m + 1)) (s : unitInterval)
        (h : y.1 (Fin.last m) = 1),
        g (y, s) = f₂ (initPt y.1, s)) := by
  classical
  have hbndm : IsClosed (Cube.boundary (Fin m)) := by
    rw [Cube.boundary]
    have h : {y : Fin m → unitInterval | ∃ i, y i = 0 ∨ y i = 1} =
        ⋃ i, ({y | y i = 0} ∪ {y | y i = 1}) := by
      ext y; simp [Set.mem_iUnion, Set.mem_union, exists_or]
    rw [h]
    exact isClosed_iUnion_of_finite (fun i =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const))
  let SA : Set (Work.StemsB.CubeBdry (m + 1) × unitInterval) :=
    {z | initPt z.1.1 ∈ Cube.boundary (Fin m)}
  let S0 : Set (Work.StemsB.CubeBdry (m + 1) × unitInterval) := {z | z.1.1 (Fin.last m) = 0}
  let S1 : Set (Work.StemsB.CubeBdry (m + 1) × unitInterval) := {z | z.1.1 (Fin.last m) = 1}
  let FA : Work.StemsB.CubeBdry (m + 1) × unitInterval → E := fun z =>
    if h : initPt z.1.1 ∈ Cube.boundary (Fin m) then
      Grim (⟨initPt z.1.1, h⟩, z.2, z.1.1 (Fin.last m))
    else f₁ (initPt z.1.1, z.2)
  let F1 : Work.StemsB.CubeBdry (m + 1) × unitInterval → E := fun z => f₁ (initPt z.1.1, z.2)
  let F2 : Work.StemsB.CubeBdry (m + 1) × unitInterval → E := fun z => f₂ (initPt z.1.1, z.2)
  let gfun : Work.StemsB.CubeBdry (m + 1) × unitInterval → E := fun z =>
    if initPt z.1.1 ∈ Cube.boundary (Fin m) then FA z
    else if z.1.1 (Fin.last m) = 0 then F1 z else F2 z
  have hF1 : Continuous F1 :=
    f₁.continuous.comp
      ((continuous_initPt_local.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hF2 : Continuous F2 :=
    f₂.continuous.comp
      ((continuous_initPt_local.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have hFA : ContinuousOn FA SA := by
    rw [continuousOn_iff_continuous_restrict]
    show Continuous (fun z : SA => FA z.1)
    have hfun : (fun z : SA => FA z.1) = fun z : SA =>
        Grim (⟨initPt z.1.1.1, z.2⟩, z.1.2, z.1.1.1 (Fin.last m)) := by
      funext z
      have hz2 : initPt z.1.1.1 ∈ Cube.boundary (Fin m) := z.2
      simp only [FA]
      rw [dif_pos hz2]
    rw [hfun]
    have hψ : Continuous fun z : SA => (⟨initPt z.1.1.1, z.2⟩ : Work.StemsB.CubeBdry m) :=
      Continuous.subtype_mk
        (continuous_initPt_local.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)))
        (fun z => z.2)
    have h2 : Continuous fun z : SA => z.1.2 := continuous_snd.comp continuous_subtype_val
    have h3 : Continuous fun z : SA => z.1.1.1 (Fin.last m) :=
      (continuous_apply (Fin.last m)).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
    exact Grim.continuous.comp (hψ.prodMk (h2.prodMk h3))
  have hSAcl : IsClosed SA := hbndm.preimage
    (continuous_initPt_local.comp (continuous_subtype_val.comp continuous_fst))
  have hS0cl : IsClosed S0 := isClosed_eq
    ((continuous_apply (Fin.last m)).comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hS1cl : IsClosed S1 := isClosed_eq
    ((continuous_apply (Fin.last m)).comp (continuous_subtype_val.comp continuous_fst)) continuous_const
  have hgSA : ContinuousOn gfun SA := by
    refine ContinuousOn.congr hFA ?_
    intro z hz
    have hz' : initPt z.1.1 ∈ Cube.boundary (Fin m) := hz
    show gfun z = FA z
    simp only [gfun]
    rw [if_pos hz']
  have hgS0 : ContinuousOn gfun S0 := by
    refine ContinuousOn.congr hF1.continuousOn ?_
    intro z hz
    have hz0 : z.1.1 (Fin.last m) = 0 := hz
    show gfun z = F1 z
    by_cases hQ : initPt z.1.1 ∈ Cube.boundary (Fin m)
    · have hgz : gfun z = FA z := by simp only [gfun]; rw [if_pos hQ]
      have hFAz : FA z = Grim (⟨initPt z.1.1, hQ⟩, z.2, z.1.1 (Fin.last m)) := by
        simp only [FA]; rw [dif_pos hQ]
      rw [hgz, hFAz, hz0]
      exact hGrim₁ ⟨initPt z.1.1, hQ⟩ z.2
    · have hgz : gfun z = (if z.1.1 (Fin.last m) = 0 then F1 z else F2 z) := by
        simp only [gfun]; rw [if_neg hQ]
      rw [hgz, if_pos hz0]
  have hgS1 : ContinuousOn gfun S1 := by
    refine ContinuousOn.congr hF2.continuousOn ?_
    intro z hz
    have hz1 : z.1.1 (Fin.last m) = 1 := hz
    show gfun z = F2 z
    by_cases hQ : initPt z.1.1 ∈ Cube.boundary (Fin m)
    · have hgz : gfun z = FA z := by simp only [gfun]; rw [if_pos hQ]
      have hFAz : FA z = Grim (⟨initPt z.1.1, hQ⟩, z.2, z.1.1 (Fin.last m)) := by
        simp only [FA]; rw [dif_pos hQ]
      rw [hgz, hFAz, hz1]
      exact hGrim₂ ⟨initPt z.1.1, hQ⟩ z.2
    · have hgz : gfun z = (if z.1.1 (Fin.last m) = 0 then F1 z else F2 z) := by
        simp only [gfun]; rw [if_neg hQ]
      rw [hgz, if_neg (by rw [hz1]; simp)]
  let S : Fin 3 → Set (Work.StemsB.CubeBdry (m + 1) × unitInterval) :=
    fun i => if i = 0 then SA else if i = 1 then S0 else S1
  have hcov : (⋃ i, S i) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases (mem_boundary_succ_last_iff z.1.1).mp z.1.2 with (h | h) | h
    · exact ⟨1, by show z.1.1 (Fin.last m) = 0; exact h⟩
    · exact ⟨2, by show z.1.1 (Fin.last m) = 1; exact h⟩
    · exact ⟨0, by show initPt z.1.1 ∈ Cube.boundary (Fin m); exact h⟩
  have hcl : ∀ i, IsClosed (S i) := by
    intro i
    fin_cases i
    · simpa [S] using hSAcl
    · simpa [S] using hS0cl
    · simpa [S] using hS1cl
  have hcontOn : ∀ i, ContinuousOn gfun (S i) := by
    intro i
    fin_cases i
    · simpa [S] using hgSA
    · simpa [S] using hgS0
    · simpa [S] using hgS1
  have hcont : Continuous gfun :=
    LocallyFinite.continuous (locallyFinite_of_finite S) hcov hcl hcontOn
  let g : C(Work.StemsB.CubeBdry (m + 1) × unitInterval, E) := ⟨gfun, hcont⟩
  have hgc : ∀ z, g z = gfun z := fun z => rfl
  have hQgz : ∀ (y : Work.StemsB.CubeBdry (m + 1)) (s : unitInterval)
      (hQ : initPt y.1 ∈ Cube.boundary (Fin m)),
      gfun (y, s) = Grim (⟨initPt y.1, hQ⟩, s, y.1 (Fin.last m)) := by
    intro y s hQ
    have h1 : gfun (y, s) = FA (y, s) := by simp only [gfun]; rw [if_pos hQ]
    rw [h1]
    simp only [FA]
    rw [dif_pos hQ]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro y s
    rw [hgc (y, s)]
    by_cases hQ : initPt y.1 ∈ Cube.boundary (Fin m)
    · rw [hQgz y s hQ]
      exact hGrim ⟨initPt y.1, hQ⟩ s (y.1 (Fin.last m))
    · have hylast : y.1 (Fin.last m) = 0 ∨ y.1 (Fin.last m) = 1 := by
        rcases (mem_boundary_succ_last_iff y.1).mp y.2 with h | h
        · exact h
        · exact absurd h hQ
      rcases hylast with h0 | h1'
      · have hgz : gfun (y, s) = f₁ (initPt y.1, s) := by
          simp only [gfun]
          rw [if_neg hQ, if_pos h0]
        rw [hgz, h0]
        exact h₁ (initPt y.1) s
      · have hgz : gfun (y, s) = f₂ (initPt y.1, s) := by
          simp only [gfun]
          rw [if_neg hQ, if_neg (by rw [h1']; simp)]
        rw [hgz, h1']
        exact h₂ (initPt y.1) s
  · intro y
    rw [hgc (y, 0)]
    by_cases hQ : initPt y.1 ∈ Cube.boundary (Fin m)
    · rw [hQgz y 0 hQ]
      exact hGrim₀ ⟨initPt y.1, hQ⟩ (y.1 (Fin.last m))
    · have hylast : y.1 (Fin.last m) = 0 ∨ y.1 (Fin.last m) = 1 := by
        rcases (mem_boundary_succ_last_iff y.1).mp y.2 with h | h
        · exact h
        · exact absurd h hQ
      rcases hylast with h0 | h1'
      · have hgz : gfun (y, 0) = f₁ (initPt y.1, 0) := by
          simp only [gfun]
          rw [if_neg hQ, if_pos h0]
        rw [hgz, h0]
        exact (c₀ (initPt y.1)).symm
      · have hgz : gfun (y, 0) = f₂ (initPt y.1, 0) := by
          simp only [gfun]
          rw [if_neg hQ, if_neg (by rw [h1']; simp)]
        rw [hgz, h1']
        exact (c₁ (initPt y.1)).symm
  · intro y s h
    rw [hgc (y, s)]
    by_cases hQ : initPt y.1 ∈ Cube.boundary (Fin m)
    · rw [hQgz y s hQ]
    · exact absurd h hQ
  · intro y s h
    rw [hgc (y, s)]
    by_cases hQ : initPt y.1 ∈ Cube.boundary (Fin m)
    · rw [hQgz y s hQ, h]
      exact hGrim₁ ⟨initPt y.1, hQ⟩ s
    · have hgz : gfun (y, s) = (if y.1 (Fin.last m) = 0 then F1 (y, s) else F2 (y, s)) := by
        simp only [gfun]; rw [if_neg hQ]
      rw [hgz, if_pos h]
  · intro y s h
    rw [hgc (y, s)]
    by_cases hQ : initPt y.1 ∈ Cube.boundary (Fin m)
    · rw [hQgz y s hQ, h]
      exact hGrim₂ ⟨initPt y.1, hQ⟩ s
    · have hgz : gfun (y, s) = (if y.1 (Fin.last m) = 0 then F1 (y, s) else F2 (y, s)) := by
        simp only [gfun]; rw [if_neg hQ]
      rw [hgz, if_neg (by rw [h]; simp)]

/-! ## The disk step from the relative homotopy lifting property -/

theorem sweepRelOfHasHLPRel {m : ℕ} {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hrel : Work.StemsB.HasHLPRel p (m + 1)) :
    Work.Serre.SweepRel m E B p := by
  intro H f₀ h₀ f₁ h₁ f₂ h₂ c₀ c₁ Grim hGrim hGrim₀ hGrim₁ hGrim₂
  classical
  have hGrimpt : ∀ (x : Work.StemsB.CubeBdry m) (a b : unitInterval),
      p (Grim (x, a, b)) = H (x.1, a, b) := fun x a b =>
    congrFun (congrArg DFunLike.coe hGrim) (x, a, b)
  have h₁pt : ∀ (x : Fin m → unitInterval) (a : unitInterval), p (f₁ (x, a)) = H (x, a, 0) :=
    fun x a => congrFun (congrArg DFunLike.coe h₁) (x, a)
  have h₂pt : ∀ (x : Fin m → unitInterval) (a : unitInterval), p (f₂ (x, a)) = H (x, a, 1) :=
    fun x a => congrFun (congrArg DFunLike.coe h₂) (x, a)
  obtain ⟨g, hglift, hg0, hgrim, hg1, hg2⟩ :=
    boundaryLiftAux p H f₀ f₁ f₂ Grim hGrimpt hGrim₀ hGrim₁ hGrim₂ h₁pt h₂pt c₀ c₁
  -- the map `H` reindexed as a homotopy with cube coordinate `I^m × I`
  let H' : C((Fin (m + 1) → unitInterval) × unitInterval, B) :=
    ⟨fun y => H (initPt y.1, y.2, y.1 (Fin.last m)),
      H.continuous.comp ((continuous_initPt_local.comp continuous_fst).prodMk
        (continuous_snd.prodMk ((continuous_apply (Fin.last m)).comp continuous_fst)))⟩
  -- the initial lift
  let f' : C(Fin (m + 1) → unitInterval, E) :=
    ⟨fun y => f₀ (initPt y, y (Fin.last m)),
      f₀.continuous.comp (continuous_initPt_local.prodMk (continuous_apply (Fin.last m)))⟩
  have hf' : p.comp f' = H'.comp (Work.StemsB.zeroIncl (m + 1)) := by
    ext y
    exact congrFun (congrArg DFunLike.coe h₀) (initPt y, y (Fin.last m))
  have hg' : p.comp g = H'.comp (Work.StemsB.bdryIncl (m + 1)) := by
    ext w
    exact hglift w.1 w.2
  have hg0' : ∀ x : Work.StemsB.CubeBdry (m + 1), g (x, 0) = f' x.1 := by
    intro x
    exact hg0 x
  obtain ⟨G', hG', hG'0, hG'bd⟩ := hrel H' f' hf' g hg' hg0'
  have hcont_snoc : Continuous fun w : (Fin m → unitInterval) × unitInterval × unitInterval =>
      snocPt w.1 w.2.2 := by
    refine continuous_pi fun i => ?_
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [snocPt_castSucc]
      exact (continuous_apply j).comp continuous_fst
    · simp only [snocPt_last]
      exact continuous_snd.comp continuous_snd
  refine ⟨⟨fun w => G' (snocPt w.1 w.2.2, w.2.1),
    G'.continuous.comp (hcont_snoc.prodMk (continuous_fst.comp continuous_snd))⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · ext w
    show p (G' (snocPt w.1 w.2.2, w.2.1)) = H w
    have h : p (G' (snocPt w.1 w.2.2, w.2.1)) = H' (snocPt w.1 w.2.2, w.2.1) :=
      congrFun (congrArg DFunLike.coe hG') (snocPt w.1 w.2.2, w.2.1)
    rw [h]
    show H (initPt (snocPt w.1 w.2.2), w.2.1, (snocPt w.1 w.2.2) (Fin.last m)) = H w
    rw [snocPt_initPt, snocPt_last]
  · intro z t
    show G' (snocPt z t, 0) = f₀ (z, t)
    rw [hG'0 (snocPt z t)]
    show f₀ (initPt (snocPt z t), (snocPt z t) (Fin.last m)) = f₀ (z, t)
    rw [snocPt_initPt, snocPt_last]
  · intro z s
    show G' (snocPt z 0, s) = f₁ (z, s)
    have hmem : snocPt z 0 ∈ Cube.boundary (Fin (m + 1)) :=
      snocPt_mem_boundary_of_last 0 (Or.inl rfl)
    rw [hG'bd ⟨snocPt z 0, hmem⟩ s]
    rw [hg1 ⟨snocPt z 0, hmem⟩ s (by simp [snocPt_last])]
    show f₁ (initPt (snocPt z 0), s) = f₁ (z, s)
    rw [snocPt_initPt]
  · intro z s
    show G' (snocPt z 1, s) = f₂ (z, s)
    have hmem : snocPt z 1 ∈ Cube.boundary (Fin (m + 1)) :=
      snocPt_mem_boundary_of_last 1 (Or.inr rfl)
    rw [hG'bd ⟨snocPt z 1, hmem⟩ s]
    rw [hg2 ⟨snocPt z 1, hmem⟩ s (by simp [snocPt_last])]
    show f₂ (initPt (snocPt z 1), s) = f₂ (z, s)
    rw [snocPt_initPt]
  · intro x u v
    show G' (snocPt x.1 v, u) = Grim (x, u, v)
    have hmem : snocPt x.1 v ∈ Cube.boundary (Fin (m + 1)) :=
      snocPt_mem_boundary_of_mem x.2 v
    rw [hG'bd ⟨snocPt x.1 v, hmem⟩ u]
    rw [hgrim ⟨snocPt x.1 v, hmem⟩ u (by rw [snocPt_initPt]; exact x.2)]
    exact congrArg Grim (Prod.ext (Subtype.ext (snocPt_initPt x.1 v))
      (Prod.ext rfl (snocPt_last x.1 v)))

end

end Work.Serre
