/-
Copyright: the martinet_totally_real_towers team.

# The invariants `H¹(N,M)^G` are the range of the inflation from `N/⟨conj⟩`

For a group extension `1 → N → G → Q → N` (`GroupExt G Q N`), a discrete `G`-module `M` on which
`G` acts trivially and an **open, surjective, continuous** homomorphism `p : N →* H` whose kernel is
the normal closure of the conjugation differences `E.conj g n * n⁻¹` (so that `H` is the largest
quotient of `N` on which `G` acts trivially), the conjugation invariants of `H¹(N, M)` -- the third
term of the five term sequence -- are exactly the classes inflated along `p`:

`H1Invariants E hcont hcompN = (H1Res p hp hcomp).range`.

Since `G` acts trivially on `M` and `hcompN` identifies the `N`-action with the `G`-action along
`i`, also `N` acts trivially on `M`, so `B¹(N,M) = 0` (`B1'_eq_bot`) and a cohomology class is
determined by its cocycle.  The proof is then purely cocycle-theoretic:

* a `1`-cocycle for a trivial action is an additive map (`hzadd`), so it vanishes on commutators;
* a class fixed by `conjH1Map g` for all `g` is *represented* by a cocycle fixed by
  `conjZ1Map g` for all `g` (here `B1 = 0` is used), hence the representing cocycle is invariant
  under the `G`-conjugation `n ↦ E.conj g n`, so it kills each `E.conj g n * n⁻¹`, hence the whole
  normal closure `ker p`);
* therefore the cocycle factors through `p`; the factorisation descends to a continuous (locally
  constant) cocycle on `H` because `p` is open and surjective, and its class maps back to the
  given class under `H1Res p` (`ker p ≤ ker p` is the well-definedness input).

The converse (every class in the range is invariant) is the computation
`p (E.conj g n) = p n`, i.e. `conjCochain` acts trivially on the inflated cocycle.
-/

import Mathlib
import Submission.Work.ConCohomology.All

set_option linter.unusedVariables false

namespace Work.ShafarevichKoch

open Function Classical

open Work.ConCohomology

/-- If `G` acts trivially on `M`, then `H¹(G,M)` is the quotient of `Z¹(G,M)` by `0`: two
`1`-cocycles with the same class are equal.  Used to descend from the conjugation action on
`H¹(N,M)` to the conjugation action on `Z¹(N,M)`. -/
lemma eq_of_H1_mk_eq_of_trivial {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [IsDiscreteGModule G M]
    (htriv : ∀ (σ : G) (m : M), σ • m = m) {z w : Z1 G M}
    (h : H1.mk z = H1.mk w) : z = w := by
  rw [H1.mk_eq_mk_iff] at h
  rw [B1'_eq_bot htriv, AddSubgroup.mem_bot] at h
  exact sub_eq_zero.mp h

theorem H1Invariants_eq_range_H1Res
    {G Q N H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [DistribMulAction G (ZMod 2)] [DistribMulAction N (ZMod 2)]
    [DistribMulAction H (ZMod 2)]
    [Work.ConCohomology.IsDiscreteGModule N (ZMod 2)]
    [Work.ConCohomology.IsDiscreteGModule H (ZMod 2)]
    (E : Work.ConCohomology.GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : ZMod 2), n • m = E.i n • m)
    (htrivG : ∀ (g : G) (m : ZMod 2), g • m = m)
    (p : N →* H) (hp : Continuous p) (hop : IsOpenMap p) (hsurj : Function.Surjective p)
    (hker : MonoidHom.ker p =
      Subgroup.normalClosure {x : N | ∃ (g : G) (n : N), x = E.conj g n * n⁻¹})
    (hcomp : ∀ (n : N) (m : ZMod 2), n • m = p n • m) :
    Work.ConCohomology.H1Invariants E hcont hcompN =
      (Work.ConCohomology.H1Res p hp hcomp).range := by
  -- `N` acts trivially on `M` (through `hcompN` and the triviality of the `G`-action), and so does
  -- `H` (through `hcomp` and the surjectivity of `p`).
  have hNtriv : ∀ (n : N) (m : ZMod 2), n • m = m := fun n m => by
    rw [hcompN n m, htrivG (E.i n) m]
  have hHtriv : ∀ (h : H) (m : ZMod 2), h • m = m := fun h m => by
    obtain ⟨n, hn⟩ := hsurj h
    rw [← hn, ← hcomp n m, hNtriv n m]
  -- the conjugates of elements of `N` lie in `ker p`, so `p` kills conjugation
  have hpmem : ∀ (g : G) (n : N), E.conj g n * n⁻¹ ∈ MonoidHom.ker p := by
    intro g n
    rw [hker]
    exact Subgroup.subset_normalClosure ⟨g, n, rfl⟩
  have hpconj : ∀ (g : G) (n : N), p (E.conj g n) = p n := by
    intro g n
    have h1 : p (E.conj g n * n⁻¹) = 1 := MonoidHom.mem_ker.mp (hpmem g n)
    calc p (E.conj g n) = p (E.conj g n * n⁻¹ * n) := by rw [inv_mul_cancel_right]
      _ = p (E.conj g n * n⁻¹) * p n := by rw [map_mul]
      _ = p n := by rw [h1, one_mul]
  apply le_antisymm
  · -- An invariant class is represented by a conjugation-invariant cocycle, which then factors
    -- through `p`; the factorisation is a cocycle on `H` whose class maps back to it.
    intro x hx
    rw [mem_H1Invariants] at hx
    revert hx
    refine QuotientAddGroup.induction_on x ?_
    intro z hfix
    -- invariance descends from `H¹` to `Z¹` because `B¹(N,M) = 0`
    have hzfix : ∀ g : G, conjZ1Map E hcont hcompN g z = z := by
      intro g
      apply eq_of_H1_mk_eq_of_trivial hNtriv
      rw [← conjH1Map_mk]
      exact hfix g
    -- consequently `z` is invariant under `n ↦ E.conj g n`
    have hzinv : ∀ (g : G) (n : N), (z : N → ZMod 2) (E.conj g n) = (z : N → ZMod 2) n := by
      intro g n
      have h : ((conjZ1Map E hcont hcompN g⁻¹ z : Z1 N (ZMod 2)) : Cochain1 N (ZMod 2)) =
          ((z : Z1 N (ZMod 2)) : Cochain1 N (ZMod 2)) :=
        congrArg (fun a : Z1 N (ZMod 2) => (a : Cochain1 N (ZMod 2))) (hzfix g⁻¹)
      rw [conjZ1Map_coe] at h
      have h2 := congrFun (congrArg (fun f : Cochain1 N (ZMod 2) => (f : N → ZMod 2)) h) n
      rw [conjCochain_apply] at h2
      simpa [htrivG] using h2
    -- with trivial action a `1`-cocycle is additive, hence vanishes on commutators
    have hzadd : ∀ a b : N, (z : N → ZMod 2) (a * b) = (z : N → ZMod 2) a + (z : N → ZMod 2) b :=
      (isCocycle1_iff_of_trivial hNtriv (z : N → ZMod 2)).mp (mem_Z1.mp z.2)
    have hz1 : (z : N → ZMod 2) 1 = 0 := isCocycle1_apply_one (mem_Z1.mp z.2)
    have hzinv1 : ∀ n : N, (z : N → ZMod 2) n⁻¹ = - (z : N → ZMod 2) n := by
      intro n
      have h := hzadd n n⁻¹
      rw [mul_inv_cancel, hz1] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    -- `z` as a homomorphism, to isolate the (normal) kernel
    let zHom : N →* Multiplicative (ZMod 2) :=
      { toFun := fun n => Multiplicative.ofAdd ((z : N → ZMod 2) n)
        map_one' := by rw [hz1, ofAdd_zero]
        map_mul' := fun a b => by rw [hzadd a b, ofAdd_add] }
    have hzker : MonoidHom.ker p ≤ MonoidHom.ker zHom := by
      rw [hker]
      refine Subgroup.normalClosure_le_normal ?_
      rintro x ⟨g, n, rfl⟩
      refine MonoidHom.mem_ker.mpr ?_
      change Multiplicative.ofAdd ((z : N → ZMod 2) (E.conj g n * n⁻¹)) = 1
      rw [ofAdd_eq_one, hzadd (E.conj g n) n⁻¹, hzinv g n, hzinv1 n, add_neg_cancel]
    have hkill : ∀ x : N, p x = 1 → (z : N → ZMod 2) x = 0 := by
      intro x hx
      have h1 : x ∈ MonoidHom.ker zHom := hzker (MonoidHom.mem_ker.mpr hx)
      have h2 : Multiplicative.ofAdd ((z : N → ZMod 2) x) = 1 := MonoidHom.mem_ker.mp h1
      exact ofAdd_eq_one.mp h2
    -- hence `z` is constant on the fibres of `p`
    have hz_factors : ∀ a b : N, p a = p b → (z : N → ZMod 2) a = (z : N → ZMod 2) b := by
      intro a b hab
      have hx : p (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
      have h0 := hkill (a * b⁻¹) hx
      rw [hzadd a b⁻¹, hzinv1 b] at h0
      have h1 : (z : N → ZMod 2) a = -(-(z : N → ZMod 2) b) := eq_neg_of_add_eq_zero_left h0
      simpa using h1
    -- the descended cocycle on `H`
    let F : H → ZMod 2 := fun h => (z : N → ZMod 2) (Classical.choose (hsurj h))
    have hFp : ∀ n : N, F (p n) = (z : N → ZMod 2) n := fun n =>
      hz_factors (Classical.choose (hsurj (p n))) n (Classical.choose_spec (hsurj (p n)))
    have hF_loc : IsLocallyConstant F := by
      rw [IsLocallyConstant.iff_exists_open]
      intro h
      obtain ⟨n, hn⟩ := hsurj h
      obtain ⟨U, hU, hnU, hUc⟩ := (z.1.isLocallyConstant).exists_open n
      refine ⟨p '' U, hop U hU, ⟨n, hnU, hn⟩, ?_⟩
      rintro h' ⟨m, hmU, rfl⟩
      rw [← hn, hFp m, hFp n]
      exact hUc m hmU
    have hF_coc : IsCocycle1 (F : H → ZMod 2) := by
      rw [isCocycle1_iff_of_trivial hHtriv]
      intro a b
      obtain ⟨m, hm⟩ := hsurj a
      obtain ⟨m', hm'⟩ := hsurj b
      rw [← hm, ← hm', ← map_mul, hFp (m * m'), hFp m, hFp m', hzadd m m']
    let Fc : Z1 H (ZMod 2) := ⟨⟨F, hF_loc⟩, mem_Z1.mpr hF_coc⟩
    refine ⟨H1.mk Fc, ?_⟩
    rw [H1Res_mk]
    change H1.mk (Z1Res p hp hcomp Fc) = H1.mk z
    rw [H1.mk_eq_mk_iff, mem_B1', mem_B1]
    refine ⟨0, ?_⟩
    ext n
    rw [d0Hom_apply, AddSubgroup.coe_sub, LocallyConstant.coe_sub, Pi.sub_apply, Z1Res_apply]
    show n • (0 : ZMod 2) - 0 = F (p n) - (z : N → ZMod 2) n
    rw [hFp n, smul_zero, sub_zero, sub_self]
  · -- Every class in the range of `H1Res p` is conjugation invariant: `p` kills conjugation.
    intro x hx
    rw [AddMonoidHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    refine QuotientAddGroup.induction_on y ?_
    intro w
    rw [mem_H1Invariants]
    intro g
    change (conjH1Map E hcont hcompN g) ((H1Res p hp hcomp) (H1.mk w)) =
      (H1Res p hp hcomp) (H1.mk w)
    rw [H1Res_mk, conjH1Map_mk]
    have hz : ((conjZ1Map E hcont hcompN g (Z1Res p hp hcomp w) : Z1 N (ZMod 2)) :
        Cochain1 N (ZMod 2)) = ((Z1Res p hp hcomp w : Z1 N (ZMod 2)) : Cochain1 N (ZMod 2)) := by
      rw [conjZ1Map_coe]
      ext n
      rw [conjCochain_apply, Z1Res_apply, htrivG g, hpconj g⁻¹ n, Z1Res_apply]
    rw [H1.mk_eq_mk_iff, B1'_eq_bot hNtriv, AddSubgroup.mem_bot, sub_eq_zero]
    exact Subtype.ext hz

end Work.ShafarevichKoch
