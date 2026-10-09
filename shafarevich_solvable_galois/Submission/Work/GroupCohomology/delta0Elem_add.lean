import Mathlib
import Submission.Work.GroupCohomology.Delta0
import Submission.Work.GroupCohomology.H1pi_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- Additivity of the connecting map `H⁰(G, C) → H¹(G, A)` on classes.  Since `delta0Cocycle`
is defined by choosing arbitrary lifts of elements of `C` along the surjection `pi`, the
difference `delta0Cocycle (c + c') - delta0Cocycle c - delta0Cocycle c'` need not vanish on the
nose, but it *is* a coboundary: the difference of the chosen lifts
`liftElem (c + c') - liftElem c - liftElem c'` lies in `ker pi = im iota`, so pulling it back
along `iota` exhibits the difference as `d⁰ a` for a single `a : A`, whence the classes agree in
`H¹`. -/
theorem delta0Elem_add {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C)
    (c c' : Work.GroupCohomology.H0 G C) :
    Work.GroupCohomology.H1π G A (S.delta0Elem (c + c')) =
      Work.GroupCohomology.H1π G A (S.delta0Elem c) +
        Work.GroupCohomology.H1π G A (S.delta0Elem c') := by
  rw [← AddMonoidHom.map_add]
  rw [H1pi_eq_iff]
  -- Choose lifts of `c`, `c'` and `c + c'` along the surjection `pi`.
  set b'' : B := S.liftElem ((c + c' : H0 G C) : C) with hb''
  set b : B := S.liftElem (c : C) with hb
  set b' : B := S.liftElem (c' : C) with hb'
  -- The difference of the lifts lands in `ker pi`.
  have hker : b'' - b - b' ∈ S.pi.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, hb'', hb, hb', S.pi_liftElem,
      S.pi_liftElem, S.pi_liftElem, AddSubgroup.coe_add]
    abel
  -- Pull it back along the inclusion `iota`.
  refine (mem_B1_iff G A _).mpr ⟨S.preimage (b'' - b - b') hker, ?_⟩
  funext g
  apply S.iota_injective
  have hia : S.iota (S.preimage (b'' - b - b') hker) = b'' - b - b' :=
    S.iota_preimage _ hker
  have hL : S.iota (d0 G A (S.preimage (b'' - b - b') hker) g)
      = g • (b'' - b - b') - (b'' - b - b') := by
    rw [d0_apply, map_sub, S.iota_equivariant, hia]
  rw [hL]
  have hce : (↑(S.delta0Elem (c + c') - (S.delta0Elem c + S.delta0Elem c') : Z1 G A) : G → A) g
      = S.delta0Cocycle (c + c') g - (S.delta0Cocycle c g + S.delta0Cocycle c' g) := rfl
  rw [hce, map_sub, map_add, S.iota_delta0Cocycle, S.iota_delta0Cocycle, S.iota_delta0Cocycle,
    ← hb'', ← hb, ← hb']
  simp only [sub_sub, smul_sub, smul_add]
  abel

end Work.GroupCohomology
