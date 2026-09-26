import Mathlib
import Submission.Work.Spike.janiszewski_pointInter
import Submission.Work.Smooth.JordanSeparation.square_lemma_aux
import Submission.Work.Spike.twoGerm
import Submission.Work.Spike.unionTwoContinuaSeparates
import Submission.Work.BoxShrink.Pinch.UnicoherencePlane
import Submission.Work.SphereJordan.homeomorph_sending_pair
import Submission.Work.JordanSeparation.janiszewskiCompactInter

namespace Work.SphereJordan

open Set
open scoped OnePoint

noncomputable section

/-- `OnePoint.some` is an injective open map with image the complement of the point at infinity.
Hence for `s` avoiding the point at infinity, the connected components of `OnePoint.some ⁻¹' s` are
the preimages of the connected components of `s`. -/

lemma image_some_preimage_eq {s : Set (OnePoint ℂ)} (hInf : (OnePoint.infty : OnePoint ℂ) ∉ s) :
    OnePoint.some '' (OnePoint.some ⁻¹' s) = s := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩; exact hz
  · intro y hy
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hInf (h ▸ hy))
    exact ⟨z, hy, rfl⟩

lemma connectedComponentIn_preimage_some {s : Set (OnePoint ℂ)}
    (hInf : (OnePoint.infty : OnePoint ℂ) ∉ s) {a : ℂ} (ha : (a : OnePoint ℂ) ∈ s) :
    connectedComponentIn (OnePoint.some ⁻¹' s) a =
      OnePoint.some ⁻¹' connectedComponentIn s (a : OnePoint ℂ) := by
  have hsub : connectedComponentIn s (a : OnePoint ℂ) ⊆ Set.range OnePoint.some := by
    intro y hy
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp
      (fun h => hInf (h ▸ connectedComponentIn_subset s (a : OnePoint ℂ) hy))
    exact ⟨z, rfl⟩
  refine Subset.antisymm ?_ ?_
  · have h1 : IsPreconnected (connectedComponentIn (OnePoint.some ⁻¹' s) a) :=
      isPreconnected_connectedComponentIn
    have h2 : IsPreconnected (OnePoint.some '' connectedComponentIn (OnePoint.some ⁻¹' s) a) :=
      h1.image _ OnePoint.continuous_coe.continuousOn
    have h3 : OnePoint.some '' connectedComponentIn (OnePoint.some ⁻¹' s) a ⊆
        connectedComponentIn s (a : OnePoint ℂ) :=
      h2.subset_connectedComponentIn ⟨a, mem_connectedComponentIn ha, rfl⟩
        (by rintro _ ⟨z, hz, rfl⟩; exact connectedComponentIn_subset (OnePoint.some ⁻¹' s) a hz)
    intro z hz
    exact h3 ⟨z, hz, rfl⟩
  · have hpre : IsPreconnected (OnePoint.some ⁻¹' connectedComponentIn s (a : OnePoint ℂ)) :=
      IsPreconnected.preimage_of_isOpenMap isPreconnected_connectedComponentIn
        OnePoint.coe_injective OnePoint.isOpenMap_coe hsub
    exact hpre.subset_connectedComponentIn (mem_connectedComponentIn ha)
      (fun z hz => connectedComponentIn_subset s (a : OnePoint ℂ) hz)

lemma component_eq_iff {s : Set (OnePoint ℂ)} (hInf : (OnePoint.infty : OnePoint ℂ) ∉ s)
    {a b : ℂ} (ha : (a : OnePoint ℂ) ∈ s) (hb : (b : OnePoint ℂ) ∈ s) :
    connectedComponentIn (OnePoint.some ⁻¹' s) a = connectedComponentIn (OnePoint.some ⁻¹' s) b ↔
      connectedComponentIn s (a : OnePoint ℂ) = connectedComponentIn s (b : OnePoint ℂ) := by
  constructor
  · intro h
    have hsub1 : connectedComponentIn s (a : OnePoint ℂ) ⊆ Set.range OnePoint.some := by
      intro y hy
      obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp
        (fun hh => hInf (hh ▸ connectedComponentIn_subset s (a : OnePoint ℂ) hy))
      exact ⟨z, rfl⟩
    have hsub2 : connectedComponentIn s (b : OnePoint ℂ) ⊆ Set.range OnePoint.some := by
      intro y hy
      obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp
        (fun hh => hInf (hh ▸ connectedComponentIn_subset s (b : OnePoint ℂ) hy))
      exact ⟨z, rfl⟩
    have h' := congrArg (fun T : Set ℂ => OnePoint.some '' T) h
    rw [connectedComponentIn_preimage_some hInf ha, connectedComponentIn_preimage_some hInf hb,
      Set.image_preimage_eq_of_subset hsub1, Set.image_preimage_eq_of_subset hsub2] at h'
    exact h'
  · intro h
    rw [connectedComponentIn_preimage_some hInf ha, connectedComponentIn_preimage_some hInf hb, h]

/-- **Reduction of the sphere form to the plane annulus form.**  If the two-point Janiszewski
statement holds for open preconnected `U, V ⊆ ℂ` with `U ∪ V = {0}ᶜ`, then it holds for open
preconnected `U, V ⊆ OnePoint ℂ` with `U ∪ V = {p,q}ᶜ` (`p ≠ q`): conjugate by a Möbius
homeomorphism carrying `p` to `0` and `q` to `∞`, and identify the complement of the point at
infinity with `ℂ`. -/
theorem twoPointJaniszewskiCover_of_plane
    (H : ∀ {U V : Set ℂ}, IsOpen U → IsOpen V → IsPreconnected U → IsPreconnected V →
      U ∪ V = ({0} : Set ℂ)ᶜ →
      ∀ x y z : ℂ, x ∈ U ∩ V → y ∈ U ∩ V → z ∈ U ∩ V →
        connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) y ∨
        connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) z ∨
        connectedComponentIn (U ∩ V) y = connectedComponentIn (U ∩ V) z)
    {U V : Set (OnePoint ℂ)} (hUo : IsOpen U) (hVo : IsOpen V)
    (hUp : IsPreconnected U) (hVp : IsPreconnected V) {p q : OnePoint ℂ} (hpq : p ≠ q)
    (hUV : U ∪ V = ({p, q} : Set (OnePoint ℂ))ᶜ) :
    ∀ x y z : OnePoint ℂ, x ∈ U ∩ V → y ∈ U ∩ V → z ∈ U ∩ V →
      connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) y ∨
      connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) z ∨
      connectedComponentIn (U ∩ V) y = connectedComponentIn (U ∩ V) z := by
  intro x y z hx hy hz
  obtain ⟨Φ, hΦp, hΦq⟩ := homeomorph_sending_pair hpq
  set U' : Set (OnePoint ℂ) := Φ '' U with hU'def
  set V' : Set (OnePoint ℂ) := Φ '' V with hV'def
  have hU'o : IsOpen U' := Φ.isOpenMap U hUo
  have hV'o : IsOpen V' := Φ.isOpenMap V hVo
  have hU'p : IsPreconnected U' := hUp.image Φ Φ.continuous.continuousOn
  have hV'p : IsPreconnected V' := hVp.image Φ Φ.continuous.continuousOn
  have h2img : Φ '' ({p, q} : Set (OnePoint ℂ)) =
      ({((0 : ℂ) : OnePoint ℂ), OnePoint.infty} : Set (OnePoint ℂ)) := by
    rw [Set.image_pair, hΦp, hΦq]
  have hUV' : U' ∪ V' = ({((0 : ℂ) : OnePoint ℂ), OnePoint.infty} : Set (OnePoint ℂ))ᶜ := by
    have h1 : U' ∪ V' = Φ '' (U ∪ V) := by rw [hU'def, hV'def, Set.image_union]
    rw [h1, hUV, Φ.image_compl, h2img]
  have hinfU : (OnePoint.infty : OnePoint ℂ) ∉ U' := by
    intro h
    have h2 : (OnePoint.infty : OnePoint ℂ) ∈ U' ∪ V' := Or.inl h
    rw [hUV'] at h2
    exact h2 (by simp)
  have hinfV : (OnePoint.infty : OnePoint ℂ) ∉ V' := by
    intro h
    have h2 : (OnePoint.infty : OnePoint ℂ) ∈ U' ∪ V' := Or.inr h
    rw [hUV'] at h2
    exact h2 (by simp)
  set A : Set ℂ := OnePoint.some ⁻¹' U' with hAdef
  set B : Set ℂ := OnePoint.some ⁻¹' V' with hBdef
  have hAo : IsOpen A := (OnePoint.isOpen_iff_of_notMem hinfU).mp hU'o
  have hBo : IsOpen B := (OnePoint.isOpen_iff_of_notMem hinfV).mp hV'o
  have hArange : U' ⊆ Set.range OnePoint.some :=
    fun y hy => OnePoint.ne_infty_iff_exists.mp (fun h => hinfU (h ▸ hy))
  have hBrange : V' ⊆ Set.range OnePoint.some :=
    fun y hy => OnePoint.ne_infty_iff_exists.mp (fun h => hinfV (h ▸ hy))
  have hAp : IsPreconnected A :=
    IsPreconnected.preimage_of_isOpenMap hU'p OnePoint.coe_injective OnePoint.isOpenMap_coe hArange
  have hBp : IsPreconnected B :=
    IsPreconnected.preimage_of_isOpenMap hV'p OnePoint.coe_injective OnePoint.isOpenMap_coe hBrange
  have hcov : A ∪ B = ({0} : Set ℂ)ᶜ := by
    have h1 : A ∪ B = OnePoint.some ⁻¹' (U' ∪ V') := by rw [hAdef, hBdef, Set.preimage_union]
    rw [h1, hUV']
    ext w
    constructor
    · intro hw h0
      rw [Set.mem_preimage, Set.mem_compl_iff, h0] at hw
      exact hw (by simp)
    · intro hw
      rw [Set.mem_preimage, Set.mem_compl_iff]
      rintro (h | h)
      · exact hw (OnePoint.coe_injective h)
      · exact absurd h (OnePoint.coe_ne_infty w)
  have hx' : Φ x ∈ U' ∩ V' := ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  have hy' : Φ y ∈ U' ∩ V' := ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  have hz' : Φ z ∈ U' ∩ V' := ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2, rfl⟩⟩
  obtain ⟨a, haeq⟩ : ∃ a : ℂ, (a : OnePoint ℂ) = Φ x :=
    OnePoint.ne_infty_iff_exists.mp (fun h => hinfU (h ▸ hx'.1))
  obtain ⟨b, hbeq⟩ : ∃ b : ℂ, (b : OnePoint ℂ) = Φ y :=
    OnePoint.ne_infty_iff_exists.mp (fun h => hinfU (h ▸ hy'.1))
  obtain ⟨c, hceq⟩ : ∃ c : ℂ, (c : OnePoint ℂ) = Φ z :=
    OnePoint.ne_infty_iff_exists.mp (fun h => hinfU (h ▸ hz'.1))
  have haI : (a : OnePoint ℂ) ∈ U' ∩ V' := by rw [haeq]; exact hx'
  have hbI : (b : OnePoint ℂ) ∈ U' ∩ V' := by rw [hbeq]; exact hy'
  have hcI : (c : OnePoint ℂ) ∈ U' ∩ V' := by rw [hceq]; exact hz'
  have haA : a ∈ A := by rw [hAdef, Set.mem_preimage]; exact haI.1
  have haB : a ∈ B := by rw [hBdef, Set.mem_preimage]; exact haI.2
  have hbA : b ∈ A := by rw [hAdef, Set.mem_preimage]; exact hbI.1
  have hbB : b ∈ B := by rw [hBdef, Set.mem_preimage]; exact hbI.2
  have hcA : c ∈ A := by rw [hAdef, Set.mem_preimage]; exact hcI.1
  have hcB : c ∈ B := by rw [hBdef, Set.mem_preimage]; exact hcI.2
  have hInterInf : (OnePoint.infty : OnePoint ℂ) ∉ U' ∩ V' := fun h => hinfU h.1
  -- transfer along `Φ.symm`
  have hU_symm : Φ.symm '' U' = U := by
    rw [hU'def]
    ext y
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨Φ y, ⟨y, hy, rfl⟩, by simp⟩
  have hV_symm : Φ.symm '' V' = V := by
    rw [hV'def]
    ext y
    constructor
    · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨Φ y, ⟨y, hy, rfl⟩, by simp⟩
  have hVU : Φ.symm '' (U' ∩ V') = U ∩ V := by
    rw [Set.image_inter Φ.symm.injective, hU_symm, hV_symm]
  have hcomp {u v : OnePoint ℂ} (huv : connectedComponentIn (U' ∩ V') u =
      connectedComponentIn (U' ∩ V') v) :
      connectedComponentIn (U ∩ V) (Φ.symm u) = connectedComponentIn (U ∩ V) (Φ.symm v) := by
    have h1 := Work.JordanSeparation.image_connectedComponentIn_homeomorph Φ.symm (U' ∩ V') u
    have h2 := Work.JordanSeparation.image_connectedComponentIn_homeomorph Φ.symm (U' ∩ V') v
    rw [huv, hVU] at h1
    rw [hVU] at h2
    rw [← h1, ← h2]
  have hstep {u v : OnePoint ℂ} (hu : u ∈ U' ∩ V') (hv : v ∈ U' ∩ V') {a b : ℂ}
      (hae : (a : OnePoint ℂ) = u) (hbe : (b : OnePoint ℂ) = v)
      (h : connectedComponentIn (OnePoint.some ⁻¹' (U' ∩ V')) a =
           connectedComponentIn (OnePoint.some ⁻¹' (U' ∩ V')) b) :
      connectedComponentIn (U' ∩ V') u = connectedComponentIn (U' ∩ V') v := by
    have h1 := (component_eq_iff hInterInf (by rw [hae]; exact hu) (by rw [hbe]; exact hv)).mp h
    rwa [hae, hbe] at h1
  have key := H hAo hBo hAp hBp hcov a b c ⟨haA, haB⟩ ⟨hbA, hbB⟩ ⟨hcA, hcB⟩
  rw [hAdef, hBdef, ← Set.preimage_inter] at key
  rcases key with h | h | h
  · exact Or.inl (by simpa using hcomp (hstep hx' hy' haeq hbeq h))
  · exact Or.inr (Or.inl (by simpa using hcomp (hstep hx' hz' haeq hceq h)))
  · exact Or.inr (Or.inr (by simpa using hcomp (hstep hy' hz' hbeq hceq h)))

end

end Work.SphereJordan
