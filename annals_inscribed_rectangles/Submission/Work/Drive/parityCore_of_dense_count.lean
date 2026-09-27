import Mathlib
import Submission.Work.Drive.countInterfaceFix
import Submission.Work.Drive.isOpen_Zc

/-!
# The counting interface with the functional identity required only on a *dense* set of parameters

`Work.Drive.parityCore_of_countOnZc` (`countInterfaceFix.lean`) needs the functional identity
(Hugelmeyer's Lemma 4) for **every** triple `(a, c, a + c)` of collision-free angles:

> `n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1`.

For the chain route that is more than the geometry gives: the engine
(`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion`,
`Work.Drive.odd_sum_topBdryMeet_clampedSweeps_of_planes`) needs *transversality* at the triple points
(`hc`, `hV`, `hface` of `Meet3Generic`, and the `trans` field of `Meet3Hyp`), and those are genericity
statements about the *given* triple of rotations.  For instance the class block `planeClassDeriv` of a
plane can genuinely fail to be injective on an open set of parameters
(`HC_VS_PLANE_IMMERSION.md`), and then `TripleTransverse` is false there (machine-checked:
`Work.Drive.not_tripleTransverseE_of_blocks_of_not_injective`).  So the identity can be out of reach at
*special* parameter triples while being provable at *generic* ones.

This file closes that gap.  The reason is that the count `n` is built from mod-2 intersection numbers
and is therefore **locally constant** in each parameter (`hn4`); a mod-2 polynomial identity in the
values of `n 0` that holds on a dense set of parameter triples consequently holds everywhere.  So the
route may prove

* `hn1` (translation invariance) and `hn2` (antisymmetry) for **all** parameters, and
* `hn3` (the functional identity) only for parameter triples in a **dense** set,

and still obtain `ParityCore γ`.  This is the formal version of the "genericity + local constancy"
resolution of the genericity inputs (`HC_AND_FACE_STATUS.md` §4,
`SURFACE_COUNT_LOCALITY_STATUS.md` §4bis).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold Topology ContDiff

noncomputable section

/-- **The functional identity on a dense set of triples suffices for `ParityCore γ`.**

`hn1`, `hn2`, `hn4` are as in `Work.Drive.parityCore_of_countOnZc`; `hdense` says that every triple
`(a, c, a + c)` of collision-free angles is a limit point of the set of triples on which the functional
identity holds.  Since the identity is a mod-2 polynomial in the locally constant values of `n 0`, the
set where it holds is a neighbourhood (inside the region `a, c, a + c ∈ Zc γ`) of each of its points,
hence it is all of that region. -/
theorem parityCore_of_countOnZc_dense {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn4 : ∀ x : Zc γ, ∀ᶠ y : Zc γ in 𝓝 x, n 0 (y : UnitAddCircle) = n 0 (x : UnitAddCircle))
    (hdense : ∀ a c : UnitAddCircle, a ∈ Zc γ → c ∈ Zc γ → a + c ∈ Zc γ →
      (a, c) ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧
          n 0 q.1 * n 0 (q.1 + q.2) + n 0 (-q.1) * n 0 q.2
            + n 0 (-(q.1 + q.2)) * n 0 (-q.2) = 1}) :
    ParityCore γ := by
  -- the identity, as a function of the parameter pair
  set Φ : UnitAddCircle × UnitAddCircle → ZMod 2 := fun q =>
    n 0 q.1 * n 0 (q.1 + q.2) + n 0 (-q.1) * n 0 q.2 + n 0 (-(q.1 + q.2)) * n 0 (-q.2) with hΦdef
  set Ω : Set (UnitAddCircle × UnitAddCircle) :=
    {q | q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ} with hΩdef
  set I : Set (UnitAddCircle × UnitAddCircle) :=
    {q | q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧ Φ q = 1} with hIdef
  -- local constancy of `n 0` in the ambient circle, from `hn4`
  have hn4amb : ∀ x : Zc γ, ∀ᶠ y : UnitAddCircle in 𝓝 (x : UnitAddCircle),
      y ∈ Zc γ → n 0 y = n 0 (x : UnitAddCircle) := by
    intro x
    have h := hn4 x
    rw [nhds_subtype] at h
    rw [Filter.eventually_comap] at h
    filter_upwards [h] with b hb hbZ
    exact hb ⟨b, hbZ⟩ rfl
  have hopen : IsOpen (Zc γ) := isOpen_Zc γ hγ
  -- `Φ` is locally constant on `Ω`
  have hloc : ∀ q ∈ Ω, ∀ᶠ p in 𝓝 q, Φ p = Φ q := by
    intro q hq
    obtain ⟨h1, h2, h12⟩ := hq
    have hp1 : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q, p.1 ∈ Zc γ :=
      (hopen.preimage continuous_fst).mem_nhds (by simpa using h1)
    have hp2 : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q, p.2 ∈ Zc γ :=
      (hopen.preimage continuous_snd).mem_nhds (by simpa using h2)
    have hp12 : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q, p.1 + p.2 ∈ Zc γ :=
      (hopen.preimage (continuous_fst.add continuous_snd)).mem_nhds (by simpa using h12)
    have e1 : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q,
        p.1 ∈ Zc γ → n 0 p.1 = n 0 q.1 :=
      (continuous_fst.tendsto q).eventually (hn4amb ⟨q.1, h1⟩)
    have e2 : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q,
        p.2 ∈ Zc γ → n 0 p.2 = n 0 q.2 :=
      (continuous_snd.tendsto q).eventually (hn4amb ⟨q.2, h2⟩)
    have e12 : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q,
        p.1 + p.2 ∈ Zc γ → n 0 (p.1 + p.2) = n 0 (q.1 + q.2) :=
      ((continuous_fst.add continuous_snd).tendsto q).eventually (hn4amb ⟨q.1 + q.2, h12⟩)
    have e1' : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q,
        -p.1 ∈ Zc γ → n 0 (-p.1) = n 0 (-q.1) :=
      (continuous_fst.neg.tendsto q).eventually (hn4amb ⟨-q.1, neg_mem_Zc h1⟩)
    have e2' : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q,
        -p.2 ∈ Zc γ → n 0 (-p.2) = n 0 (-q.2) :=
      (continuous_snd.neg.tendsto q).eventually (hn4amb ⟨-q.2, neg_mem_Zc h2⟩)
    have e12' : ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 q,
        -(p.1 + p.2) ∈ Zc γ → n 0 (-(p.1 + p.2)) = n 0 (-(q.1 + q.2)) :=
      ((continuous_fst.add continuous_snd).neg.tendsto q).eventually
        (hn4amb ⟨-(q.1 + q.2), neg_mem_Zc h12⟩)
    filter_upwards [hp1, hp2, hp12, e1, e2, e12, e1', e2', e12'] with p k1 k2 k12 f1 f2 f12 f1' f2' f12'
    rw [hΦdef]
    dsimp only
    rw [f1 k1, f2 k2, f12 k12, f1' (neg_mem_Zc k1), f2' (neg_mem_Zc k2), f12' (neg_mem_Zc k12)]
  -- hence the identity holds on all of `Ω`
  have hn3 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1 := by
    intro a ha c hc hac
    have hΩ : (a, c) ∈ Ω := ⟨ha, hc, hac⟩
    have hmem : (a, c) ∈ closure I := by
      simpa [hIdef, hΦdef] using hdense a c ha hc hac
    obtain ⟨U, hUeq, hUopen, hUmem⟩ := eventually_nhds_iff.mp (hloc (a, c) hΩ)
    have hne : (U ∩ I).Nonempty := mem_closure_iff.mp hmem U hUopen hUmem
    obtain ⟨p, hpU, hpI⟩ := hne
    have hval : Φ (a, c) = 1 := by
      rw [← hUeq p hpU]
      exact hpI.2.2.2
    rw [hΦdef] at hval
    simpa using hval
  exact parityCore_of_countOnZc n hn1 hn2 hn3 hn4

end

end Work.Drive
