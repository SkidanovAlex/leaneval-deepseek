import Mathlib
import Submission.Work.ORLyndon.Fox
import Submission.Work.OROneRel.HNNStep

/-!
# Chain rule for Fox derivatives, and the Fox derivative of `zeta` (clean copy)

This is a **verbatim copy, into the namespace `Work.ORLyndon.FoxZeta`, of the declarations of
`Submission/Work/OROneRel/foxD_zeta_of_ne.lean`** (node N2), taken for *import hygiene only*: the
original file imports `Submission.Work.OROneRel.RhoRewrite`, which declares `Work.OROneRel.rew`, a
name already declared in `Submission.Work.OROneRel.MagnusGenDefs`.  Any module whose import closure
contains both files fails to elaborate with

`import ...RhoRewrite failed, environment already contains 'Work.OROneRel.rew' from ...MagnusGenDefs`

and the `ORLyndon` chain (`powDefs` -> `kms_torsion_at` -> `magnus_step_root` ->
`coverRootDefs` -> `MagnusGenDefs`) contains the second of the two.  Since none of the declarations
below uses anything from `RhoRewrite`, the copy drops that import and keeps the `ORLyndon` chain
buildable.

**This file can be deleted** (and the three `ORLyndon` modules importing it switched back to
`Submission.Work.OROneRel.foxD_zeta_of_ne`) as soon as the name `Work.OROneRel.rew` is renamed or
namespaced in one of its two homes -- see the note in
`Submission/Work/OROneRel/magnus_step_root.lean`.
-/

namespace Work.ORLyndon.FoxZeta

open MonoidAlgebra

theorem mdrh_of {X Y : Type*} {K : Type*} [Semiring K]
    (φ : FreeGroup X →* FreeGroup Y) (g : FreeGroup X) :
    (MonoidAlgebra.mapDomainRingHom K φ) (MonoidAlgebra.of K (FreeGroup X) g) =
      MonoidAlgebra.of K (FreeGroup Y) (φ g) := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.of_apply]

theorem chain_letters {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {K : Type*} [Ring K] (φ : FreeGroup X →* FreeGroup Y) (y : Y) (L : List (X × Bool)) :
    (Work.ORLyndon.letters L).sum (fun x =>
        (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxWord (K := K) x L) *
          Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x)))
      = Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.mk L)) := by
  induction L with
  | nil =>
      simp [Work.ORLyndon.letters, ← FreeGroup.one_eq_mk]
  | cons c L ih =>
      obtain ⟨z, b⟩ := c
      rw [Work.ORLyndon.letters_cons]
      have hkey : ∀ x : X,
          (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxWord (K := K) x ((z,b) :: L)) *
            Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x))
          = ((MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxLetter (K := K) x (z,b)) *
                Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x)))
            + (MonoidAlgebra.of K (FreeGroup Y) (φ (Work.ORLyndon.letterGroup (z,b)))) *
                (((MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxWord (K := K) x L)) *
                  Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x))) := by
        intro x
        rw [Work.ORLyndon.foxWord_cons]
        simp only [map_add, map_mul, add_mul, mul_assoc]
        rw [mdrh_of (K := K) φ (Work.ORLyndon.letterGroup (z,b))]
      have hG : (insert z (Work.ORLyndon.letters L)).sum (fun x =>
            (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxLetter (K := K) x (z,b)) *
              Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x)))
          = (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxLetter (K := K) z (z,b)) *
              Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of z)) := by
        refine Finset.sum_eq_single z ?_ ?_
        · intro b' _ hb'
          rw [show Work.ORLyndon.foxLetter (K := K) b' (z,b) = 0 from
            Work.ORLyndon.foxLetter_eq_zero_of_ne (K := K) (x := b') (y := z)
              (fun h : z = b' => hb' h.symm) b]
          simp
        · intro h; exact absurd (Finset.mem_insert_self z (Work.ORLyndon.letters L)) h
      have hGz : (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxLetter (K := K) z (z,b)) *
              Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of z))
          = Work.ORLyndon.foxD (K := K) y (φ (Work.ORLyndon.letterGroup (z,b))) := by
        cases b
        · have hfl : Work.ORLyndon.foxLetter (K := K) z (z, false) =
              -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of z)⁻¹)) := by
            rw [Work.ORLyndon.foxLetter_false, if_pos rfl]
          have hlg : Work.ORLyndon.letterGroup (z, false) = (FreeGroup.of z)⁻¹ := rfl
          rw [hfl, hlg, map_neg, mdrh_of, map_inv, Work.ORLyndon.foxD_inv, neg_mul]
        · have hfl : Work.ORLyndon.foxLetter (K := K) z (z, true) = 1 := by
            rw [Work.ORLyndon.foxLetter_true, if_pos rfl]
          have hlg : Work.ORLyndon.letterGroup (z, true) = FreeGroup.of z := rfl
          rw [hfl, hlg, map_one, one_mul]
      have hF : (Work.ORLyndon.letters L).sum (fun x =>
            (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxWord (K := K) x L) *
              Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x)))
          = (insert z (Work.ORLyndon.letters L)).sum (fun x =>
            (MonoidAlgebra.mapDomainRingHom K φ) (Work.ORLyndon.foxWord (K := K) x L) *
              Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of x))) := by
        refine Finset.sum_subset ?_ ?_
        · intro x hx; exact Finset.mem_insert_of_mem hx
        · intro x _ hx
          rw [Work.ORLyndon.foxWord_eq_zero_of_notMem hx]
          simp
      rw [Finset.sum_congr rfl (fun x _ => hkey x), Finset.sum_add_distrib, hG,
        ← Finset.mul_sum, ← hF, ih, hGz,
        ← Work.ORLyndon.letterGroup_mul_mk (z,b) L, map_mul, Work.ORLyndon.foxD_mul]

theorem chain_rule {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {K : Type*} [Ring K] (φ : FreeGroup X →* FreeGroup Y) (y : Y) (w : FreeGroup X) :
    Work.ORLyndon.foxD (K := K) y (φ w) =
      (Work.ORLyndon.foxFD (K := K) w).sum (fun q c =>
        (MonoidAlgebra.mapDomainRingHom K φ) c *
          Work.ORLyndon.foxD (K := K) y (φ (FreeGroup.of q))) := by
  induction w using Quot.inductionOn with
  | h L =>
      rw [FreeGroup.quot_mk_eq_mk, ← chain_letters (K := K) φ y L]
      have hs : (Work.ORLyndon.foxFD (K := K) (FreeGroup.mk L)).support ⊆
          Work.ORLyndon.letters L := by
        intro q hq
        by_contra hqL
        exact (Finsupp.mem_support_iff.mp hq) (by
          rw [Work.ORLyndon.foxFD_mk, Work.ORLyndon.foxWord_eq_zero_of_notMem hqL])
      rw [Finsupp.sum_of_support_subset _ hs _ (by intro i _; simp)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Work.ORLyndon.foxFD_mk]

/-- The Fox derivative of an integer power is zero when the derivative of the base is zero. -/
theorem foxD_zpow_eq_zero {X : Type*} [DecidableEq X] {K : Type*} [Ring K]
    (x : X) (g : FreeGroup X) (n : ℤ) (h : Work.ORLyndon.foxD (K := K) x g = 0) :
    Work.ORLyndon.foxD (K := K) x (g ^ n) = 0 := by
  let H : Subgroup (FreeGroup X) :=
    { carrier := {a | Work.ORLyndon.foxD (K := K) x a = 0}
      mul_mem' := by
        intro a b ha hb
        show Work.ORLyndon.foxD (K := K) x (a * b) = 0
        rw [Work.ORLyndon.foxD_mul, show Work.ORLyndon.foxD (K := K) x a = 0 from ha,
            show Work.ORLyndon.foxD (K := K) x b = 0 from hb, mul_zero, add_zero]
      one_mem' := by
        show Work.ORLyndon.foxD (K := K) x (1 : FreeGroup X) = 0
        exact Work.ORLyndon.foxD_one x
      inv_mem' := by
        intro a ha
        show Work.ORLyndon.foxD (K := K) x a⁻¹ = 0
        rw [Work.ORLyndon.foxD_inv, show Work.ORLyndon.foxD (K := K) x a = 0 from ha,
            mul_zero, neg_zero] }
  have hmem : g ∈ H := h
  exact H.zpow_mem hmem n

theorem zeta_of_eval {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t x : α) (hxt : x ≠ t) (q : {a : α // a ≠ t} × ℤ) :
    Work.ORLyndon.foxD (K := K) x (Work.OROneRel.zeta t (FreeGroup.of q)) =
      if (q.1 : α) = x then
        MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
      else 0 := by
  have ht : Work.ORLyndon.foxD (K := K) x (FreeGroup.of t) = 0 := by
    rw [Work.ORLyndon.foxD_of, if_neg (Ne.symm hxt)]
  have hA : Work.ORLyndon.foxD (K := K) x ((FreeGroup.of t) ^ (q.2)) = 0 :=
    foxD_zpow_eq_zero x (FreeGroup.of t) q.2 ht
  have hC : Work.ORLyndon.foxD (K := K) x ((FreeGroup.of t) ^ (-(q.2))) = 0 :=
    foxD_zpow_eq_zero x (FreeGroup.of t) (-(q.2)) ht
  rw [Work.OROneRel.zeta, FreeGroup.lift_apply_of]
  rw [Work.ORLyndon.foxD_mul, Work.ORLyndon.foxD_mul]
  rw [hA, hC, Work.ORLyndon.foxD_of, map_mul]
  by_cases hq : (q.1 : α) = x <;> simp [hq]

theorem foxD_zeta_of_ne {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t x : α) (hxt : x ≠ t) (w : FreeGroup ({a : α // a ≠ t} × ℤ)) :
    Work.ORLyndon.foxD (K := K) x (Work.OROneRel.zeta t w) =
      (Work.ORLyndon.foxFD (K := K) w).sum (fun q c =>
        if (q.1 : α) = x then
          (MonoidAlgebra.mapDomainRingHom K (Work.OROneRel.zeta t)) c *
            MonoidAlgebra.of K (FreeGroup α) ((FreeGroup.of t) ^ (q.2))
        else 0) := by
  rw [chain_rule (K := K) (Work.OROneRel.zeta t) x w]
  refine Finsupp.sum_congr (fun q _ => ?_)
  rw [zeta_of_eval t x hxt q, mul_ite, mul_zero]

end Work.ORLyndon.FoxZeta
