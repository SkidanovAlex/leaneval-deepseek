import Mathlib
import Submission.Work.Cohomology.SingIn
import Submission.Work.Cohomology.chainMap_singIn
import Submission.Work.Cohomology.chainMap_sup
import Submission.Work.Cover.exists_small_cycle_homologous
import Submission.Work.Cover.exists_small_boundary
import Submission.Work.Cohomology.Pairing

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

noncomputable section

/-! ## Auxiliary lemmas about the inclusion of a subcomplex

The three lemmas below are the degreewise input of the proof of the small-simplex theorem: the
pushforward of chains along the inclusion of a subcomplex is injective, a chain of a subcomplex
whose image in the ambient complex is a cycle is itself a cycle, and a coboundary pairs to zero
with every cycle. -/

/-- The pushforward of chains along the inclusion of a subcomplex is injective, because the
inclusion is injective on the simplices of every degree. -/
private lemma chainMap_ι_injective (S : SSet.{0}) (C : S.Subcomplex) (n : ℕ) :
    Function.Injective (chainMap ℚ C.ι n) := by
  intro a b h
  exact Finsupp.mapDomain_injective (injective_ι_subcomplex S C n)
    (by simpa only [chainMap, Finsupp.lmapDomain_apply] using h)

/-- A chain of a subcomplex whose image under the inclusion is a cycle of the ambient complex is
itself a cycle: the pushforward of chains commutes with the boundary and is injective. -/
private lemma mem_chainCycles_of_chainMap_ι (S : SSet.{0}) (C : S.Subcomplex) {k : ℕ}
    {c'' : SChain C ℚ k} {c' : SChain S ℚ k} (h : chainMap ℚ C.ι k c'' = c')
    (hc' : c' ∈ chainCycles S ℚ k) : c'' ∈ chainCycles C ℚ k := by
  match k with
  | 0 => exact Submodule.mem_top
  | m + 1 =>
      rw [mem_chainCycles_succ]
      have h2 : (chainMap ℚ C.ι m) ((sbdry C.toSSet ℚ m) c'')
          = (chainMap ℚ C.ι m) 0 := by
        rw [chainMap_sbdry ℚ C.ι m c'', h, mem_chainCycles_succ.mp hc', map_zero]
      exact chainMap_ι_injective S C m h2

/-- A cochain which is a coboundary pairs to zero with every cycle. -/
private lemma seval_eq_zero_of_mem_boundaries {S : SSet.{0}} {n : ℕ}
    {v : Cochain S ℚ n} (hv : v ∈ boundaries S ℚ n) {c : SChain S ℚ n}
    (hc : c ∈ chainCycles S ℚ n) : seval S ℚ n v c = 0 := by
  match n with
  | 0 =>
      rw [boundaries, Submodule.mem_bot] at hv
      rw [hv]
      simp [seval_apply]
  | m + 1 =>
      obtain ⟨w, hw⟩ := (mem_boundaries_succ v).mp hv
      rw [← hw]
      exact seval_coboundary_eq_zero w c hc

/-- **The small-simplex theorem, injectivity half.**  Let `X` be a topological space with an open
cover `X = U ∪ V` and let `small := singIn X U ⊔ singIn X V` be the subcomplex of singular
simplices landing in `U` or in `V`.  Then the restriction map
`H (Sing X) ℚ k → H small ℚ k` is injective.

Proof plan.  Take a cocycle `u : Cochain (Sing X) ℚ k` and suppose that its restriction
`pullbackCo ℚ small.ι u` is a coboundary of `small` (this is exactly the hypothesis
`H.map ℚ small.ι k (H.mk u hu) = 0`, by `H.map_mk` and `H.mk_eq_mk_iff`).  By
`Work.Cohomology.mem_boundaries_of_forall_chainCycles_seval_eq_zero` it suffices to prove
`seval (Sing X) ℚ k u c = 0` for every cycle `c` of `Sing X`.  Given `c`, apply
`Work.Cover.exists_small_cycle_homologous` to get a cycle `c'` with
`c' ∈ chainIn X U k ⊔ chainIn X V k` and a chain `d` with `sbdry d = c' - c`; then
`seval u c = seval u c' - seval u (sbdry d) = seval u c' - seval (coboundary u) d = seval u c'`.
Now `c'` lies in `range (chainMap ℚ small.ι k)`, which is computed by
`Work.Cohomology.chainMap_sup` and `Work.Cohomology.chainMap_singIn` to be
`chainIn X U k ⊔ chainIn X V k`; so `c' = chainMap ℚ small.ι k c''` for a unique `c''`, which is
itself a cycle of `small` (apply `chainMap_sbdry` and the injectivity part of
`chainMap_sup`/`chainMap_singIn`).  Finally `seval (Sing X) ℚ k u c' = seval small ℚ k
(pullbackCo ℚ small.ι u) c''` by `Work.Cohomology.seval_chainMap`, and this is zero because the
pullback is a coboundary of `small` and `c''` is a cycle
(`Work.Cohomology.seval_coboundary_eq_zero`). -/
theorem small_simplex_injective (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x, x ∈ U ∨ x ∈ V) (k : ℕ) :
    Function.Injective (Submission.Cohomology.H.map ℚ
      (Submission.Cohomology.singIn X U ⊔ Submission.Cohomology.singIn X V).ι k) := by
  set S : SSet := TopCat.toSSet.obj X
  set small : S.Subcomplex := singIn X U ⊔ singIn X V
  -- It suffices to show that a class whose restriction vanishes is zero.
  have key : ∀ z : H S ℚ k, H.map ℚ small.ι k z = 0 → z = 0 := by
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | _ u =>
      rw [Submodule.Quotient.mk_eq_zero]
      -- the restriction of the representative is a coboundary of `small`
      have hz' : H.mk (pullbackCo ℚ small.ι u.1) (pullbackCo_mem_cycles small.ι u.2) = 0 := by
        rw [← H.map_mk ℚ small.ι u.1 u.2]
        exact hz
      have hpull : pullbackCo ℚ small.ι u.1 ∈ boundaries small ℚ k := by
        have hmem := (Submodule.Quotient.mk_eq_zero (p := boundariesInCycles small ℚ k)).mp hz'
        simpa only [boundariesInCycles, Submodule.mem_comap, Submodule.subtype_apply] using hmem
      -- it remains to see that the representative pairs to zero with every cycle of `S`
      have hvanish : ∀ c, c ∈ chainCycles S ℚ k → seval S ℚ k u.1 c = 0 := by
        intro c hc
        -- replace `c` by a homologous small cycle `c'`
        obtain ⟨c', hc'mem, d, hd⟩ :=
          Work.Cover.exists_small_cycle_homologous X U V hU hV hUV k c hc
        -- `c'` is a cycle, because it differs from `c` by the boundary `sbdry d`
        have hc'cyc : c' ∈ chainCycles S ℚ k := by
          have hbd : c' - c ∈ chainCycles S ℚ k :=
            chainBoundaries_le_chainCycles S k ⟨d, hd⟩
          have := Submodule.add_mem _ hc hbd
          rwa [add_sub_cancel] at this
        -- `c'` is the image of a chain `c''` of the small complex
        have hrange : c' ∈ (chainMap ℚ small.ι k).range := by
          rw [(chainMap_sup S (singIn X U) (singIn X V) k).1,
            (chainMap_singIn X U k).1, (chainMap_singIn X V k).1]
          exact hc'mem
        obtain ⟨c'', hc''⟩ := hrange
        have hc''cyc : c'' ∈ chainCycles small ℚ k :=
          mem_chainCycles_of_chainMap_ι S small hc'' hc'cyc
        -- `u` takes the same value on `c` and on `c'`, since `c' - c` is a boundary
        have h1 : seval S ℚ k u.1 c = seval S ℚ k u.1 c' := by
          have h0 : seval S ℚ k u.1 (c' - c) = 0 := by
            rw [← hd, ← seval_coboundary S ℚ k u.1 d, LinearMap.mem_ker.mp u.2]
            simp [seval_apply]
          have hsub : seval S ℚ k u.1 (c' - c)
              = seval S ℚ k u.1 c' - seval S ℚ k u.1 c := by
            simp only [map_sub]
          rw [hsub] at h0
          exact (sub_eq_zero.mp h0).symm
        -- and the value on `c'` is that of the pullback on `c''`, which is a coboundary
        have h2 : seval S ℚ k u.1 c' = seval small ℚ k (pullbackCo ℚ small.ι u.1) c'' := by
          rw [← hc'']
          exact seval_chainMap ℚ small.ι k u.1 c''
        have h3 : seval small ℚ k (pullbackCo ℚ small.ι u.1) c'' = 0 :=
          seval_eq_zero_of_mem_boundaries hpull hc''cyc
        rw [h1, h2, h3]
      have hwb : u.1 ∈ boundaries S ℚ k :=
        mem_boundaries_of_forall_chainCycles_seval_eq_zero u.1 hvanish
      rw [boundariesInCycles, Submodule.mem_comap]
      simpa using hwb
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  exact key z (LinearMap.mem_ker.mp hz)

end

end Work.Cohomology
