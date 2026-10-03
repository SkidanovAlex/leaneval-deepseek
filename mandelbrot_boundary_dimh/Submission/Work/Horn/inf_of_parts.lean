import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.Horn.surj_aux

/-!
# AREA HORN — infinite degree of the horn map: the `inf` conjuncts from the analytic pieces

Assembly of `HornData.inf_u` / `HornData.inf_l` from the two pieces that are actually available at
this stage of the route (see `NOTES_LEAD_horn.md`, "Assembly by the HORN owner"):

* `himage`  (the "Claim B ⇒ φ onto" step): `B ∖ critOrbit f₀ c ⊆ φ '' BuOf` and `⊆ φ '' BlOf`;
* `hPhiinf` (Claim A, `Φ : B → ℂ` has infinite fibres): every horizontal fibre
  `{z ∈ B | Φ z = y}` is infinite.

The argument.  `E = Φ ∘ φ` is the lifted horn map and `Bu = BuOf d B` is `T`-invariant with
`Bu ⊆ d.DE` (`hTopo`), so on the fibre `{w ∈ Bu | E w = y}` the map `π(w) = exp(2πiw)` is
INJECTIVE (`Work.Horn.piExp_injOn_E_fiber`): two points of a fibre differing by an integer would
force `y = y + k`.  Hence it suffices to show that this fibre is infinite.

Fix `y`.  The `Φ`-fibre `F = {z ∈ B | Φ z = y}` is infinite by `hPhiinf`.  Its intersection with
the forward critical orbit is finite: `Φ (f^k c) = Φ c + k` (`Work.Horn.Phi_critOrbit`), so at
most one `k` can satisfy `Φ (f^k c) = y`.  Hence `F ∖ critOrbit` is infinite.  Every point of it
has a `φ`-preimage in `Bu` (`himage`); choosing one gives an injection of `F ∖ critOrbit` into
`{w ∈ Bu | E w = y}`, so that fibre is infinite, and so is its `π`-image.

The same argument with `Bl = BlOf d B` (`himage.2`) gives the lower conjunct.
-/

namespace Work.Horn

noncomputable section

open _root_.MandelDim

/-- One side of the assembly: from `B ∖ critOrbit ⊆ φ '' Bu` (and `Bu` `T`-invariant inside `d.DE`,
which is what makes `π` injective on `E`-fibres) plus infinite `Φ`-fibres, the `E`-fibres over
every point of `Bu` have infinite `π`-image. -/
theorem inf_image_of_parts {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    {Bu : Set ℂ} (hφBu : B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' Bu)
    (hTG : MandelDim.IsTInvariant Bu) (hDE : Bu ⊆ d.DE)
    (hPhiinf : ∀ y : ℂ, {z : ℂ | z ∈ B ∧ d.Φ z = y}.Infinite) :
    ∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ Bu ∧ d.E w = y}).Infinite := by
  intro y
  have hFinf : ({z : ℂ | z ∈ B ∧ d.Φ z = y}).Infinite := hPhiinf y
  -- the part of the `Φ`-fibre lying on the forward critical orbit is finite
  have hcritfin : (MandelDim.critOrbit f₀ c ∩ {z : ℂ | z ∈ B ∧ d.Φ z = y}).Finite := by
    have hbas : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
    have hmaps := hsetup.2.1.2.2.2.2.1
    have hcB : c ∈ B := hsetup.2.2.1
    have hPhi : ∀ k : ℕ, d.Φ (f₀^[k] c) = d.Φ c + (k : ℂ) :=
      Work.Horn.Phi_critOrbit d hbas hmaps hcB
    -- at most one `k` has `Φ (f^k c) = y`
    have hKsub : ({k : ℕ | 1 ≤ k ∧ d.Φ (f₀^[k] c) = y}).Subsingleton := by
      intro k hk l hl
      have h1 : d.Φ (f₀^[k] c) = d.Φ (f₀^[l] c) := by rw [hk.2, hl.2]
      rw [hPhi k, hPhi l] at h1
      exact_mod_cast add_left_cancel h1
    refine Set.Finite.subset ((hKsub.finite).image (fun k : ℕ => f₀^[k] c)) ?_
    rintro z ⟨hzcrit, hzF⟩
    obtain ⟨k, hk1, hkz⟩ := hzcrit
    exact ⟨k, ⟨hk1, by rw [← hkz]; exact hzF.2⟩, hkz.symm⟩
  have hSinf : ({z : ℂ | z ∈ B ∧ d.Φ z = y} \ MandelDim.critOrbit f₀ c).Infinite := by
    have h := hFinf.sdiff hcritfin
    rwa [Set.sdiff_inter_self_eq_sdiff] at h
  -- choose a `φ`-preimage in `Bu` for every point of the (infinite) punctured fibre
  have hφBu' : ∀ z : ℂ, z ∈ B \ MandelDim.critOrbit f₀ c → ∃ w : ℂ, w ∈ Bu ∧ d.φ w = z :=
    fun z hz => hφBu hz
  classical
  let g : ℂ → ℂ := fun z => if h : z ∈ B \ MandelDim.critOrbit f₀ c then
      Classical.choose (hφBu' z h) else 0
  have hg : ∀ z (hz : z ∈ B \ MandelDim.critOrbit f₀ c), g z ∈ Bu ∧ d.φ (g z) = z := by
    intro z hz
    have h1 : g z = Classical.choose (hφBu' z hz) := by
      dsimp only [g]; rw [dite_eq_left hz]
    rw [h1]
    exact Classical.choose_spec (hφBu' z hz)
  -- the chosen preimages land in the `E`-fibre over `y` and `π` is injective there
  have hinj : Set.InjOn (fun z => MandelDim.piExp (g z))
      ({z : ℂ | z ∈ B ∧ d.Φ z = y} \ MandelDim.critOrbit f₀ c) := by
    intro z hz z' hz' heq
    have hzmem : z ∈ B \ MandelDim.critOrbit f₀ c := ⟨hz.1.1, hz.2⟩
    have hz'mem : z' ∈ B \ MandelDim.critOrbit f₀ c := ⟨hz'.1.1, hz'.2⟩
    have hgz2 := (hg z hzmem).2
    have hgz'2 := (hg z' hz'mem).2
    have hmemz : g z ∈ {w : ℂ | w ∈ Bu ∧ d.E w = y} := by
      refine ⟨(hg z hzmem).1, ?_⟩
      show d.Φ (d.φ (g z)) = y
      rw [hgz2]; exact hz.1.2
    have hmemz' : g z' ∈ {w : ℂ | w ∈ Bu ∧ d.E w = y} := by
      refine ⟨(hg z' hz'mem).1, ?_⟩
      show d.Φ (d.φ (g z')) = y
      rw [hgz'2]; exact hz'.1.2
    have heq' : g z = g z' := (Work.Horn.piExp_injOn_E_fiber d hTG hDE) hmemz hmemz' heq
    rw [← hgz2, heq', hgz'2]
  have hYinf : ((fun z => MandelDim.piExp (g z)) '' ({z : ℂ | z ∈ B ∧ d.Φ z = y} \
      MandelDim.critOrbit f₀ c)).Infinite := by
    by_contra h
    rw [Set.not_infinite] at h
    exact hSinf (Set.Finite.of_finite_image h hinj)
  refine hYinf.mono ?_
  rintro p ⟨z, hz, rfl⟩
  have hzmem : z ∈ B \ MandelDim.critOrbit f₀ c := ⟨hz.1.1, hz.2⟩
  refine ⟨g z, ⟨(hg z hzmem).1, ?_⟩, rfl⟩
  show d.Φ (d.φ (g z)) = y
  rw [(hg z hzmem).2]; exact hz.1.2

theorem inf_of_parts (hTopo : MandelDim.HornTopoStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (himage : (B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BuOf d B) ∧
      (B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BlOf d B))
    (hPhiinf : ∀ y : ℂ, {z : ℂ | z ∈ B ∧ d.Φ z = y}.Infinite) :
    (∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = y}).Infinite) ∧
      (∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BlOf d B ∧ d.E w = y}).Infinite) := by
  obtain ⟨-, -, hBuT, hBlT, -, -, hDE⟩ := hTopo f₀ D₀ B c d hsetup
  exact ⟨inf_image_of_parts d hsetup himage.1 hBuT (fun w hw => hDE (Or.inl hw)) hPhiinf,
    inf_image_of_parts d hsetup himage.2 hBlT (fun w hw => hDE (Or.inr hw)) hPhiinf⟩

end

end Work.Horn
