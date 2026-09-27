import Mathlib
import Submission.Work.Geo.Radial.Basic

/-!
# The corrected chart-push lemma (with `[T2Space M]`)

The requested lemma `Work.Geo.Radial.exists_chart_push`
(`Submission/Work/Geo/Radial/exists_chart_push.lean`) is **false as stated**: it is missing a
separation hypothesis on `M`.  A counterexample (the line with two origins, in every dimension
`n ≥ 1`) is written out in that file.

This file contains the repaired statement, with `[T2Space M]` added — the hypothesis under which
the lemma is used, since the applications take `M` to be a metric space.  The statement is
otherwise identical to the requested one; see `Work.Geo.Radial.exists_chart_push_t2` below.

The proof uses `[T2Space M]` only through `IsCompact.isClosed`, applied to the support
`c.toFun '' ccubeAround q (S + δ)` of the push, which makes that support closed so that the
pushed map (identity off the support) is continuous.
-/

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

/-- Geometry: a cube around `q` of radius `S` is inside `PL.openCube R` as soon as `S + m < R`. -/
private lemma ccubeAround_subset_openCube' {n : ℕ} {q : PL.E n} {m S R : ℝ}
    (hq : ∀ i, |q i| ≤ m) (hSR : S + m < R) : ccubeAround q S ⊆ PL.openCube R := by
  intro y hy i
  have hyi : |y i - q i| ≤ S := hy i
  have hqi : |q i| ≤ m := hq i
  calc |y i| = |(y i - q i) + q i| := by ring_nf
    _ ≤ |y i - q i| + |q i| := abs_add_le _ _
    _ ≤ S + m := by linarith
    _ < R := hSR

/-- **Corrected form of `exists_chart_push`**: the requested statement with the separation
hypothesis `[T2Space M]` added (this is the hypothesis under which the lemma is used, and it is
needed: see the discussion above).

The intended fully-qualified name is `Work.Geo.Radial.exists_chart_push_t2`. -/
theorem exists_chart_push_t2 {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (c : PL.CubeChart n M)
    {q : EuclideanSpace ℝ (Fin n)} {m S τ : ℝ} (hq : ∀ i, |q i| ≤ m) (hmS : m ≤ S)
    (hSτ : S + m < τ) (hτ1 : τ < 1)
    (H : unitInterval → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hcont : Continuous fun p : unitInterval × EuclideanSpace ℝ (Fin n) => (H p.1) p.2)
    (hH0 : H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin n)))
    (hid : ∀ s y, y ∉ ocubeAround q S → (H s) y = y)
    (hmaps : ∀ s y, y ∈ ocubeAround q S → (H s) y ∈ ocubeAround q S) :
    ∃ h : unitInterval → M ≃ₜ M,
      (Continuous fun p : unitInterval × M => (h p.1) p.2) ∧
      h 0 = Homeomorph.refl M ∧
      (∀ s p, p ∉ c.toFun '' PL.openCube τ → (h s) p = p) ∧
      (∀ s y, y ∈ PL.openCube τ →
        (H s) y ∈ PL.openCube 1 ∧ (h s) (c.toFun y) = c.toFun ((H s) y)) := by
  classical
  have hsub1 : PL.openCube τ ⊆ PL.openCube (n := n) 1 := fun y hy i => lt_trans (hy i) hτ1
  -- the image of any open piece of the chart cube is open in `M`
  have image_open : ∀ {ρ : ℝ} {V : Set (PL.E n)}, ρ < 1 → IsOpen V →
      IsOpen (c.toFun '' (PL.openCube ρ ∩ V)) := by
    intro ρ V hρ hV
    have hsubρ : PL.openCube ρ ⊆ PL.openCube (n := n) 1 := fun y hy i => lt_trans (hy i) hρ
    have hρopen : IsOpen (PL.openCube (n := n) ρ) := by
      rw [← ocubeAround_zero]; exact isOpen_ocubeAround 0 ρ
    have hVsub : IsOpen (PL.openCube ρ ∩ V) := hρopen.inter hV
    have hSopen : IsOpen ((Subtype.val : ↥(PL.openCube 1) → PL.E n) ⁻¹' (PL.openCube ρ ∩ V)) :=
      hVsub.preimage continuous_subtype_val
    obtain ⟨U, hUopen, hUeq⟩ := c.emb.toIsEmbedding.isInducing.image_eq_isOpen_inter_range hSopen
    have hEq : c.toFun '' (PL.openCube ρ ∩ V)
        = U ∩ Set.range ((PL.openCube 1).domRestrict c.toFun) := by
      rw [← hUeq]
      refine Set.Subset.antisymm ?_ ?_
      · rintro p ⟨y, hy, rfl⟩
        exact ⟨⟨y, hsubρ hy.1⟩, hy, rfl⟩
      · rintro p ⟨x, hx, hx'⟩
        exact ⟨x.1, hx, hx'⟩
    rw [hEq]
    exact hUopen.inter c.emb.isOpen_range
  -- a small margin keeping the closed cube strictly inside `PL.openCube τ`
  set δ : ℝ := (τ - (S + m)) / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hSδτ : S + δ + m < τ := by rw [hδdef]; linarith
  have hKsub : ccubeAround q (S + δ) ⊆ PL.openCube τ := ccubeAround_subset_openCube' hq hSδτ
  have hKsub1 : ccubeAround q (S + δ) ⊆ PL.openCube (n := n) 1 := fun y hy => hsub1 (hKsub hy)
  have hocube_sub : ocubeAround q S ⊆ ccubeAround q (S + δ) :=
    fun y hy i => le_of_lt (lt_of_lt_of_le (hy i) (by linarith))
  -- the chart image of `openCube τ` (the support of the push) and the support compactum
  set Oset : Set M := c.toFun '' PL.openCube τ with hOdef
  set Kset : Set M := c.toFun '' ccubeAround q (S + δ) with hKdef
  have himg : ∀ (y : PL.E n), y ∈ PL.openCube τ → c.toFun y ∈ Oset := fun y hy => ⟨y, hy, rfl⟩
  have hinj : ∀ {y z : PL.E n}, y ∈ PL.openCube 1 → z ∈ PL.openCube 1 →
      c.toFun y = c.toFun z → y = z := by
    intro y z hy hz h
    have h' : (PL.openCube 1).domRestrict c.toFun ⟨y, hy⟩ =
        (PL.openCube 1).domRestrict c.toFun ⟨z, hz⟩ := h
    exact congrArg Subtype.val (c.emb.toIsEmbedding.injective h')
  -- the inverse chart map on the support
  let inv : M → PL.E n := fun p => if h : p ∈ Oset then Classical.choose h else 0
  have inv_mem : ∀ {p : M} (hp : p ∈ Oset), inv p ∈ PL.openCube τ := by
    intro p hp
    have h := (Classical.choose_spec hp).1
    dsimp only [inv]
    rwa [dite_eq_left hp]
  have inv_spec : ∀ {p : M} (hp : p ∈ Oset), c.toFun (inv p) = p := by
    intro p hp
    have h := (Classical.choose_spec hp).2
    dsimp only [inv]
    rwa [dite_eq_left hp]
  have inv_apply : ∀ {y : PL.E n} (hy : y ∈ PL.openCube τ), inv (c.toFun y) = y := by
    intro y hy
    have hmem : c.toFun y ∈ Oset := himg y hy
    exact hinj (hsub1 (inv_mem hmem)) (hsub1 hy) (inv_spec hmem)
  have hOopen : IsOpen Oset := by
    rw [hOdef]
    simpa only [Set.inter_univ] using image_open (ρ := τ) (V := Set.univ) hτ1 isOpen_univ
  have hKcompact : IsCompact Kset := by
    have hco : ContinuousOn c.toFun (ccubeAround q (S + δ)) := c.cont.mono hKsub1
    have h := (isCompact_ccubeAround q (S + δ)).image_of_continuousOn hco
    rw [hKdef]; exact h
  -- this is the only use of the separation hypothesis
  have hKclosed : IsClosed Kset := hKcompact.isClosed
  have hKinO : Kset ⊆ Oset := by
    rintro p ⟨y, hy, rfl⟩
    exact himg y (hKsub hy)
  have hinv_cont : ContinuousOn inv Oset := by
    rw [continuousOn_open_iff hOopen]
    intro t ht
    have heq : Oset ∩ inv ⁻¹' t = c.toFun '' (PL.openCube τ ∩ t) := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro p ⟨hp, hpt⟩
        exact ⟨inv p, ⟨inv_mem hp, hpt⟩, inv_spec hp⟩
      · rintro p ⟨y, ⟨hy, hyt⟩, rfl⟩
        refine ⟨himg y hy, ?_⟩
        show inv (c.toFun y) ∈ t
        rw [inv_apply hy]; exact hyt
    rw [heq]
    exact image_open hτ1 ht
  -- `H s` keeps the cube `PL.openCube τ` inside itself, and so does its inverse
  have H_open : ∀ s : unitInterval, ∀ y ∈ PL.openCube τ, (H s) y ∈ PL.openCube τ := by
    intro s y hy
    by_cases hmem : y ∈ ocubeAround q S
    · exact hKsub (hocube_sub (hmaps s y hmem))
    · rw [hid s y hmem]; exact hy
  have Hsymm_open : ∀ s : unitInterval, ∀ y ∈ PL.openCube τ, (H s).symm y ∈ PL.openCube τ := by
    intro s y hy
    by_cases hmem : (H s).symm y ∈ ocubeAround q S
    · exact hKsub (hocube_sub hmem)
    · have hfix : (H s) ((H s).symm y) = (H s).symm y := hid s ((H s).symm y) hmem
      rw [Homeomorph.apply_symm_apply] at hfix
      rw [← hfix]; exact hy
  have Hsymm_fix : ∀ s : unitInterval, ∀ y ∉ ocubeAround q S, (H s).symm y = y := by
    intro s y hy
    have hfix : (H s) y = y := hid s y hy
    calc (H s).symm y = (H s).symm ((H s) y) := by rw [hfix]
      _ = y := Homeomorph.symm_apply_apply _ _
  -- the pushed map and its inverse, as explicit formulas
  let F : unitInterval → M → M := fun s p => if p ∈ Oset then c.toFun ((H s) (inv p)) else p
  let Fi : unitInterval → M → M :=
    fun s p => if p ∈ Oset then c.toFun ((H s).symm (inv p)) else p
  have F_apply : ∀ (s : unitInterval) {p : M}, p ∈ Oset → F s p = c.toFun ((H s) (inv p)) := by
    intro s p hp; dsimp only [F]; exact ite_eq_left hp
  have F_off : ∀ (s : unitInterval) {p : M}, p ∉ Oset → F s p = p := by
    intro s p hp; dsimp only [F]; exact ite_eq_right hp
  have Fi_apply : ∀ (s : unitInterval) {p : M}, p ∈ Oset →
      Fi s p = c.toFun ((H s).symm (inv p)) := by
    intro s p hp; dsimp only [Fi]; exact ite_eq_left hp
  have Fi_off : ∀ (s : unitInterval) {p : M}, p ∉ Oset → Fi s p = p := by
    intro s p hp; dsimp only [Fi]; exact ite_eq_right hp
  have F_off_K : ∀ (s : unitInterval) (p : M), p ∉ Kset → F s p = p := by
    intro s p hK
    by_cases hO : p ∈ Oset
    · have hinv : inv p ∉ ccubeAround q (S + δ) := fun hc => hK ⟨inv p, hc, inv_spec hO⟩
      have hnot : inv p ∉ ocubeAround q S := fun hc => hinv (hocube_sub hc)
      rw [F_apply s hO, hid s (inv p) hnot, inv_spec hO]
    · exact F_off s hO
  have Fi_off_K : ∀ (s : unitInterval) (p : M), p ∉ Kset → Fi s p = p := by
    intro s p hK
    by_cases hO : p ∈ Oset
    · have hinv : inv p ∉ ccubeAround q (S + δ) := fun hc => hK ⟨inv p, hc, inv_spec hO⟩
      have hnot : inv p ∉ ocubeAround q S := fun hc => hinv (hocube_sub hc)
      rw [Fi_apply s hO, Hsymm_fix s (inv p) hnot, inv_spec hO]
    · exact Fi_off s hO
  -- joint continuity of the family `F`
  have hF_joint : Continuous fun p : unitInterval × M => F p.1 p.2 := by
    refine continuous_of_cover_nhds (s := fun b : Bool =>
      bif b then Set.univ ×ˢ Oset else Set.univ ×ˢ Ksetᶜ) ?_ ?_
    · intro p
      by_cases hp : p.2 ∈ Oset
      · exact ⟨true, (isOpen_univ.prod hOopen).mem_nhds ⟨trivial, hp⟩⟩
      · exact ⟨false, (isOpen_univ.prod hKclosed.isOpen_compl).mem_nhds
          ⟨trivial, fun hk => hp (hKinO hk)⟩⟩
    · intro b
      cases b with
      | false =>
        refine ContinuousOn.congr continuous_snd.continuousOn ?_
        intro q hq
        exact F_off_K q.1 q.2 hq.2
      | true =>
        have hpair : ContinuousOn (fun q : unitInterval × M => (q.1, inv q.2))
            (Set.univ ×ˢ Oset) :=
          (continuous_fst.continuousOn).prodMk
            (hinv_cont.comp continuous_snd.continuousOn (fun _ hq => hq.2))
        have h1 : ContinuousOn (fun q : unitInterval × M => (H q.1) (inv q.2))
            (Set.univ ×ˢ Oset) := hcont.comp_continuousOn hpair
        have h2 : ContinuousOn (fun q : unitInterval × M => c.toFun ((H q.1) (inv q.2)))
            (Set.univ ×ˢ Oset) :=
          c.cont.comp h1 (fun q hq => hsub1 (H_open q.1 (inv q.2) (inv_mem hq.2)))
        refine ContinuousOn.congr h2 ?_
        intro q hq
        exact F_apply q.1 hq.2
  have hcontF : ∀ s : unitInterval, Continuous (F s) := fun s =>
    hF_joint.comp (continuous_const.prodMk continuous_id)
  have hcontFi : ∀ s : unitInterval, Continuous (Fi s) := by
    intro s
    refine continuous_of_cover_nhds (s := fun b : Bool => bif b then Oset else Ksetᶜ) ?_ ?_
    · intro p
      by_cases hp : p ∈ Oset
      · exact ⟨true, hOopen.mem_nhds hp⟩
      · exact ⟨false, hKclosed.isOpen_compl.mem_nhds (fun hk => hp (hKinO hk))⟩
    · intro b
      cases b with
      | false =>
        refine ContinuousOn.congr continuous_id.continuousOn ?_
        intro p hp
        exact Fi_off_K s p hp
      | true =>
        have h1 : ContinuousOn (fun p : M => (H s).symm (inv p)) Oset :=
          (H s).symm.continuous.comp_continuousOn hinv_cont
        have h2 : ContinuousOn (fun p : M => c.toFun ((H s).symm (inv p))) Oset :=
          c.cont.comp h1 (fun p hp => hsub1 (Hsymm_open s (inv p) (inv_mem hp)))
        refine ContinuousOn.congr h2 ?_
        intro p hp
        exact Fi_apply s hp
  -- the two formulas are mutually inverse
  have hleft : ∀ s : unitInterval, Function.LeftInverse (Fi s) (F s) := by
    intro s p
    by_cases hO : p ∈ Oset
    · have hinv : inv p ∈ PL.openCube τ := inv_mem hO
      have hmem2 : c.toFun ((H s) (inv p)) ∈ Oset := himg _ (H_open s _ hinv)
      rw [F_apply s hO, Fi_apply s hmem2, inv_apply (H_open s _ hinv),
        Homeomorph.symm_apply_apply, inv_spec hO]
    · rw [F_off s hO, Fi_off s hO]
  have hright : ∀ s : unitInterval, Function.RightInverse (Fi s) (F s) := by
    intro s p
    by_cases hO : p ∈ Oset
    · have hinv : inv p ∈ PL.openCube τ := inv_mem hO
      have hmem2 : c.toFun ((H s).symm (inv p)) ∈ Oset := himg _ (Hsymm_open s _ hinv)
      rw [Fi_apply s hO, F_apply s hmem2, inv_apply (Hsymm_open s _ hinv),
        Homeomorph.apply_symm_apply, inv_spec hO]
    · rw [Fi_off s hO, F_off s hO]
  let h : unitInterval → M ≃ₜ M := fun s =>
    Homeomorph.mk (toEquiv := ⟨F s, Fi s, hleft s, hright s⟩) (hcontF s) (hcontFi s)
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · exact hF_joint
  · refine Homeomorph.ext (fun p => ?_)
    show F 0 p = p
    by_cases hO : p ∈ Oset
    · rw [F_apply 0 hO, hH0]
      simpa only [Homeomorph.refl_apply, id_eq] using inv_spec hO
    · exact F_off 0 hO
  · intro s p hp
    exact F_off s (fun hh => hp (hOdef ▸ hh))
  · intro s y hy
    refine ⟨hsub1 (H_open s y hy), ?_⟩
    have hmem : c.toFun y ∈ Oset := himg y hy
    show F s (c.toFun y) = c.toFun ((H s) y)
    rw [F_apply s hmem, inv_apply hy]

end Work.Geo.Radial
