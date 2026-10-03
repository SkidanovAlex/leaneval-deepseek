import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.flatten_replicate_getElem_mod
import Submission.Work.OROneRel.isReduced_rotate_of_isCyclicallyReduced
import Submission.Work.OROneRel.append_take_rotate_drop

/-!
# Complementing a subword of a power of a cyclically reduced relator

Let `r` be a cyclically reduced relator (so its reduced word `W = r.toWord` is cyclically reduced,
hence every rotation of `W` is also reduced and the powers `r ^ k` have reduced word
`W ++ W ++ ... ++ W`).  Let `v` be a subword of `r ^ k` whose reduced word `V` is shorter than `W`.
Then `V` occurs inside a window of length `|W|` of the periodic word `W^∞`, so it is a prefix of
some rotation `W.rotate j` of `W`; writing `W.rotate j = V ++ S` we get

`v * mk S = mk (W.rotate j) = u * r * u⁻¹` for a suitable `u`,

with `S` a subword of `W ++ W` (whence `IsSubwordOf (mk S) (r ^ 2)`), `|S| = |W| - |V|`, and
`S ≠ []`.  This is the "complement" of the subword `v`, used to prolong a Weinbaum/Magnus style
argument from a short subword to a full conjugate of the relator.

The proof factors into a purely combinatorial list statement
(`eq_rotate_take_of_flatten_replicate_eq`) together with elementary free-group algebra.
-/

namespace Work.OROneRel

universe u

/-- **The combinatorial core.**  Suppose the periodic word `W ++ W ++ ... ++ W` (`k` copies) is
written as `L₁ ++ V ++ L₂` and `V` is no longer than `W`.  Then `V` is the prefix of the rotation
of `W` starting at the position `L₁.length` of the periodic word; equivalently `V` is the length
`|V|` initial segment of `W.rotate L₁.length`. -/
theorem eq_rotate_take_of_flatten_replicate_eq {α : Type u} {W V L₁ L₂ : List α} {k : ℕ}
    (h : (List.replicate k W).flatten = L₁ ++ V ++ L₂) (hlen : V.length ≤ W.length) :
    V = (W.rotate L₁.length).take V.length := by
  apply List.ext_getElem?
  intro m
  by_cases hm : m < V.length
  · -- `m` lies inside the block `V`: compare the two ends of the `getElem?` identity, using the
    -- periodicity of `(replicate k W).flatten`.
    have hrot : (List.take V.length (W.rotate L₁.length))[m]? = W[(m + L₁.length) % W.length]? := by
      rw [List.getElem?_take_of_lt hm, List.getElem?_rotate (lt_of_lt_of_le hm hlen)]
    have hsub : V[m]? = ((List.replicate k W).flatten)[L₁.length + m]? := by
      rw [h, List.append_assoc, List.getElem?_append_right (Nat.le_add_right L₁.length m),
        Nat.add_sub_cancel_left, List.getElem?_append_left hm]
    have hper : ((List.replicate k W).flatten)[L₁.length + m]? = W[(L₁.length + m) % W.length]? :=
      flatten_replicate_getElem_mod (by rw [h, List.length_append, List.length_append]; omega)
    rw [hrot, hsub, hper, Nat.add_comm L₁.length m]
  · -- both sides are out of range
    have h1 : (List.take V.length (W.rotate L₁.length)).length ≤ m := by
      rw [List.length_take, List.length_rotate, Nat.min_eq_left hlen]; omega
    have h2 : V.length ≤ m := by omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

theorem exists_complement_of_isSubwordOf_pow {α : Type u} {r v : FreeGroup α} {k : ℕ}
    (hr : Work.OROneRel.IsCyclicallyReducedRelator r)
    (h : Work.OROneRel.IsSubwordOf v (r ^ k))
    (hlen : Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm r) :
    ∃ (u s : FreeGroup α),
      v * s = u * r * u⁻¹ ∧
      Work.OROneRel.relatorNorm (v * s) = Work.OROneRel.relatorNorm r ∧
      Work.OROneRel.relatorNorm s = Work.OROneRel.relatorNorm r - Work.OROneRel.relatorNorm v ∧
      Work.OROneRel.IsSubwordOf s (r ^ 2) ∧ s ≠ 1 := by
  classical
  -- reduced words
  obtain ⟨L1, L2, hL⟩ := h
  set W := FreeGroup.toWord r with hW
  set Vw := FreeGroup.toWord v with hVw
  have hrcyc : FreeGroup.IsCyclicallyReduced W := by
    show FreeGroup.IsCyclicallyReduced (FreeGroup.toWord r)
    exact hr
  -- the reduced word of `r ^ k` is `W ++ W ++ ... ++ W`
  have hflat : FreeGroup.toWord (r ^ k) = (List.replicate k W).flatten := by
    rw [FreeGroup.toWord_pow, ← hW]
    exact (FreeGroup.isReduced_iff_reduce_eq).mp (hrcyc.flatten_replicate k).isReduced
  have hmain : (List.replicate k W).flatten = L1 ++ Vw ++ L2 := by rw [← hflat, hL]
  have hlt : Vw.length < W.length := by
    have h' := hlen
    simp only [relatorNorm, FreeGroup.norm] at h'
    rwa [← hVw, ← hW] at h'
  have hWpos : 0 < W.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  -- `Vw` is a prefix of a rotation of `W`
  have htake : Vw = (W.rotate L1.length).take Vw.length :=
    eq_rotate_take_of_flatten_replicate_eq hmain (le_of_lt hlt)
  -- cut the cyclic word at the position of `Vw`
  set n := L1.length % W.length with hn
  have hnle : n ≤ W.length := by rw [hn]; exact le_of_lt (Nat.mod_lt _ hWpos)
  set T := W.rotate n with hT
  have hTn : T = W.rotate L1.length := by rw [hT, hn, List.rotate_mod]
  set S := T.drop Vw.length with hS
  have hVS : Vw ++ S = T := by
    have h1 : T = T.take Vw.length ++ S := by
      rw [hS]; exact (List.take_append_drop Vw.length T).symm
    rw [h1, hTn, ← htake]
  have hTred : FreeGroup.IsReduced T := by
    rw [hT]; exact isReduced_rotate_of_isCyclicallyReduced hrcyc n
  have hSred : FreeGroup.IsReduced S :=
    hTred.infix ⟨Vw, [], by rw [← hVS, List.append_nil]⟩
  -- the two pieces of the cut rotation
  set A := W.take n with hA
  set B := W.drop n with hB
  have hWAB : W = A ++ B := by rw [hA, hB]; exact (List.take_append_drop n W).symm
  have hTBA : T = B ++ A := by rw [hT, hA, hB, List.rotate_eq_drop_append_take hnle]
  -- group elements
  have hv : v = FreeGroup.mk Vw := by rw [hVw]; exact (FreeGroup.mk_toWord (x := v)).symm
  have hrW : r = FreeGroup.mk W := by rw [hW]; exact (FreeGroup.mk_toWord (x := r)).symm
  have hvs : v * FreeGroup.mk S = FreeGroup.mk T := by
    rw [hv, FreeGroup.mul_mk, hVS]
  have htwo : FreeGroup.toWord (r ^ 2) = W ++ W := by
    have hcyc : FreeGroup.IsCyclicallyReduced (List.flatten (List.replicate 2 W)) :=
      hrcyc.flatten_replicate 2
    rw [FreeGroup.toWord_pow, ← hW]
    rw [(FreeGroup.isReduced_iff_reduce_eq).mp hcyc.isReduced]
    simp [List.replicate_succ]
  -- lengths
  have hnorm_r : relatorNorm r = W.length := by rw [relatorNorm, FreeGroup.norm, ← hW]
  have hnorm_v : relatorNorm v = Vw.length := by rw [relatorNorm, FreeGroup.norm, ← hVw]
  have hnorm_mkT : relatorNorm (FreeGroup.mk T) = relatorNorm r := by
    rw [hnorm_r, relatorNorm, FreeGroup.norm, FreeGroup.toWord_mk, hTred.reduce_eq, hT,
      List.length_rotate]
  have hnorm_mkS : relatorNorm (FreeGroup.mk S) = S.length := by
    rw [relatorNorm, FreeGroup.norm, FreeGroup.toWord_mk, hSred.reduce_eq]
  -- the complement and its conjugator
  refine ⟨(FreeGroup.mk A)⁻¹, FreeGroup.mk S, ?_, ?_, ?_, ?_, ?_⟩
  · -- `v * mk S = mk T = (mk A)⁻¹ * r * mk A`
    rw [hvs, hrW, inv_inv, hWAB, hTBA, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
    group
  · -- `|v * mk S| = |r|`
    rw [hvs, hnorm_mkT]
  · -- `|mk S| = |r| - |v|`
    rw [hnorm_mkS, hS, List.length_drop, hT, List.length_rotate, hnorm_r, hnorm_v]
  · -- `mk S` is a subword of `r ^ 2`
    refine ⟨W.take n ++ Vw, W.drop n, ?_⟩
    have hrot : W.rotate n = Vw ++ S := hT.symm.trans hVS.symm
    calc FreeGroup.toWord (r ^ 2)
        = W ++ W := htwo
      _ = W.take n ++ W.rotate n ++ W.drop n := append_take_rotate_drop W hnle
      _ = W.take n ++ (Vw ++ S) ++ W.drop n := by rw [hrot]
      _ = (W.take n ++ Vw) ++ S ++ W.drop n := by simp only [List.append_assoc]
      _ = (W.take n ++ Vw) ++ FreeGroup.toWord (FreeGroup.mk S) ++ W.drop n := by
            rw [FreeGroup.toWord_mk, hSred.reduce_eq]
  · -- `mk S ≠ 1`
    intro h1
    have hpos : 0 < relatorNorm (FreeGroup.mk S) := by
      rw [hnorm_mkS, hS, List.length_drop, hT, List.length_rotate]
      omega
    rw [h1] at hpos
    simp [relatorNorm, FreeGroup.norm] at hpos

end Work.OROneRel
