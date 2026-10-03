import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.ann_rootVec_of_level
import Submission.Work.ORLyndon.levelPart_rootVec_eq_base
import Submission.Work.ORLyndon.sigma_zeta_eq_one
import Submission.Work.ORLyndon.levelOf_support_mapDomainRingHom_zeta
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.HNNStep
import Submission.Work.ORLyndon.base_regularity_transport
import Submission.Work.ORLyndon.mmHi_mem_relatorLetters

/-!
# The Magnus step of the Cohen--Lyndon induction in the exponent-sum-zero case

The Cohen--Lyndon theorem is proved by induction along the Magnus hierarchy of a one-relator group.
This file assembles the **exponent-sum-zero step** of that induction in a form that is independent
of *which* Magnus rewriting is used:

* the induction hypothesis at the base is taken as an explicit hypothesis (`hIH`/`hIHord`), the base
  being the one-relator group `⟨β | (magRewRel t u) ^ l⟩` on the decorated alphabet
  `β = ({a // a ≠ t} × ℤ)`;
* the embedding of the base into `⟨α | r⟩` is taken as an explicit injective homomorphism
  `m : ⟨β | (magRewRel t u) ^ l⟩ →* ⟨α | r⟩` which is compatible with the Magnus rewriting
  (`hcomp`);

everything else is proved here.

The mathematical content is the **leading-level transfer** of
`Submission/Work/ORLyndon/ann_rootVec_of_level.lean`: with `G = ⟨α | r⟩`, `r = u ^ l`, `σ_t u = 1`,
the group algebra `K[G]` is a twisted Laurent polynomial ring over the base `K[B]`, `B = ker σ_t`, so
the highest-level part of the equation `b * (∂u/∂x) = 0` is the equation
`c * (∂v/∂(x,i)) = 0` in the base — and the base Fox derivative is right regular by the induction
hypothesis.

The pieces supplied here are:

* `Work.ORLyndon.foxD_eq_zero_of_notMem_relatorLetters` — the Fox derivative vanishes on a symbol
  that does not occur in the word;
* `Work.ORLyndon.level_le_of_foxD_eq_zero` — the maximum level occurring in the `x`-component of the
  root Fox vector is at most the largest decoration `i` for which `∂v/∂(x,i) ≠ 0` (the level bound
  `hDbound` of the transfer);
* `Work.ORLyndon.range_eq_ker_levelOf` — the range of the embedding of the base is the kernel of the
  level map (this is what makes the transported regularity applicable to base-supported elements);
* `Work.ORLyndon.orderOf_of_magnusStep` — the order of the class of the root is unchanged
  (`orderOf (presentRho r u) = l` from `orderOf` in the base), the order half of the induction;
* `Work.ORLyndon.ann_rootVec_of_magnusStep` — the leading-level transfer with all its inputs;
* `Work.ORLyndon.lyndon_independence_of_pow_eps_zero` — the assembled step.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type*} [DecidableEq α] {K : Type*} [Field K]

/-- **The decorated alphabet `β = ({a // a ≠ t} × ℤ)`** of the Magnus rewriting. -/
abbrev MagnusBeta (t : α) := ({a : α // a ≠ t} × ℤ)

/-- **The relator of the Magnus base**: `(magRewRel t u) ^ l`. -/
noncomputable abbrev magRewRelPow (t : α) (u : FreeGroup α) (l : ℕ) : FreeGroup (MagnusBeta t) :=
  Work.OROneRel.magRewRel t u ^ l

/-- **The Magnus base** `⟨β | (magRewRel t u) ^ l⟩`. -/
abbrev MagnusBase (t : α) (u : FreeGroup α) (l : ℕ) : Type _ :=
  PresentedGroup ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))

/-- `FreeGroup.toWord` does not depend on the `DecidableEq` instance with which it is computed. -/
theorem toWord_eq_of_decEq (i j : DecidableEq α) (v : FreeGroup α) :
    @FreeGroup.toWord α i v = @FreeGroup.toWord α j v := by
  have h : i = j := funext fun a => funext fun b => Subsingleton.elim _ _
  rw [h]

/-- A word has vanishing Fox derivative at `q` as soon as `q` occurs in it nowhere. -/
theorem foxWord_eq_zero_of_forall_not_mem (q : α) {L : List (α × Bool)}
    (h : ∀ b : Bool, (q, b) ∉ L) : foxWord (K := K) q L = 0 := by
  refine foxWord_eq_zero_of_notMem ?_
  intro hmem
  obtain ⟨b, hb⟩ : ∃ b : Bool, (q, b) ∈ L := by
    simpa [letters, List.mem_toFinset, List.mem_map] using hmem
  exact h b hb

/-- The Fox derivative of a word vanishes on a symbol that does not occur in it. -/
theorem foxD_eq_zero_of_notMem_relatorLetters (q : α) (v : FreeGroup α)
    (h : q ∉ Work.OROneRel.relatorLetters v) :
    foxD (K := K) q v = 0 := by
  have hq : ∀ b : Bool, (q, b) ∉ @FreeGroup.toWord α (Classical.decEq α) v := by
    intro b hb
    exact h (by rw [Work.OROneRel.relatorLetters]; exact ⟨b, hb⟩)
  have hqc : ∀ b : Bool, (q, b) ∉ FreeGroup.toWord v := by
    intro b hb
    refine hq b ?_
    rwa [toWord_eq_of_decEq (inferInstance : DecidableEq α) (Classical.decEq α) v] at hb
  calc foxD (K := K) q v = foxD (K := K) q (FreeGroup.mk (FreeGroup.toWord v)) := by
        rw [FreeGroup.mk_toWord]
    _ = 0 := foxWord_eq_zero_of_forall_not_mem q hqc

section Level

variable {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
variable {hσ : Work.OROneRel.sigma t u = 1}

/-- **The level-`j` part of the root Fox vector vanishes above the last decoration.**  If the Fox
derivative `∂v/∂(x,j)` of the Magnus rewriting vanishes (which happens when `(x,j)` is not a
decoration occurring in it), then the `j`-th level part of the `x`-component of the root Fox vector
vanishes, by the chain rule `Work.ORLyndon.levelPart_rootVec_eq_base`. -/
theorem levelPart_eq_zero_of_foxD_eq_zero {x : α} (hxt : x ≠ t) {j : ℤ}
    (h : foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0) :
    levelPart t r u l hpow hσ j (rootVec K r u x) = 0 := by
  rw [levelPart_rootVec_eq_base t x hxt r u l hpow hσ j, h, map_zero, zero_mul]

/-- **The level bound.**  If every decoration `j > i` of the letter `x` is absent from the Magnus
rewriting of `u` (i.e. `∂v/∂(x,j) = 0`), then every level occurring in the `x`-component of the root
Fox vector is at most `i`.  This is the hypothesis `hDbound` of the leading-level transfer. -/
theorem level_le_of_foxD_eq_zero {x : α} (hxt : x ≠ t) {i : ℤ}
    (hdec : ∀ j : ℤ, i < j →
      foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0) :
    ∀ g ∈ (rootVec K r u x).coeff.support, (levelOf t r u l hpow hσ g).toAdd ≤ i := by
  intro g hg
  by_contra hcon
  have hj : i < (levelOf t r u l hpow hσ g).toAdd := lt_of_not_ge hcon
  have hzero := levelPart_eq_zero_of_foxD_eq_zero (K := K) (t := t) (r := r) (u := u) (l := l)
    (hpow := hpow) (hσ := hσ) hxt (hdec _ hj)
  have hcoeff : (levelPart t r u l hpow hσ ((levelOf t r u l hpow hσ g).toAdd)
      (rootVec K r u x)).coeff g = 0 := by rw [hzero]; rfl
  rw [levelPart_coeff, if_pos] at hcoeff
  · exact (Finsupp.mem_support_iff.mp hg) hcoeff
  · exact (ofAdd_toAdd (levelOf t r u l hpow hσ g)).symm

end Level

section Base

variable {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
variable {hσ : Work.OROneRel.sigma t u = 1}

/-- The exponent sums `Work.OROneRel.sigma t` and `Work.OROneRel.expSum t` agree. -/
theorem sigma_eq_expSum (t : α) : Work.OROneRel.sigma t = Work.OROneRel.expSum t := rfl

/-- The Magnus embeddings `Work.OROneRel.zeta t` and `Work.OROneRel.magnusMap t` agree. -/
theorem zeta_eq_magnusMap (t : α) : Work.OROneRel.zeta t = Work.OROneRel.magnusMap t := rfl

/-- **The range of the Magnus base is the kernel of the level map.**  Let `m` be the embedding of the
Magnus base `⟨β | (magRewRel t u) ^ l⟩` into `G = ⟨α | r⟩` compatible with the Magnus rewriting
(`hcomp`).  Then its range is exactly the Magnus base `ker (levelOf)` of `G`.

The inclusion `⊆` is `σ_t` vanishing on the image of `ζ_t`; the reverse inclusion uses that the
kernel of the exponent sum in `t` is the image of the Magnus embedding
(`Work.OROneRel.magRange_eq_ker`). -/
theorem range_eq_ker_levelOf (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1)
    (m : MagnusBase t u l →* OneRelatorGroup r)
    (hcomp : m.comp (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t)) :
    ∀ g : OneRelatorGroup r, g ∈ m.range ↔ levelOf t r u l hpow hσ g = 1 := by
  intro g
  constructor
  · rintro ⟨h, rfl⟩
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
      ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t))) h
    have h1 := DFunLike.congr_fun hcomp w
    simp only [MonoidHom.comp_apply] at h1
    rw [h1, levelOf_presentRho t r u l hpow hσ]
    exact sigma_zeta_eq_one t w
  · intro hg
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective ({r} : Set (FreeGroup α)) g
    have hw : Work.OROneRel.expSum t w = 1 := by
      rw [← sigma_eq_expSum t, ← levelOf_presentRho t r u l hpow hσ w]
      exact hg
    have hmem : w ∈ (Work.OROneRel.magnusMap t).range := by
      rw [Work.OROneRel.magRange_eq_ker t]
      exact MonoidHom.mem_ker.mpr hw
    obtain ⟨w', hw'⟩ := hmem
    refine ⟨PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t))) w', ?_⟩
    have h1 : m (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t))) w')
        = presentRho r (Work.OROneRel.zeta t w') := by
      have h2 := DFunLike.congr_fun hcomp w'
      simpa only [MonoidHom.comp_apply] using h2
    have h3 : presentRho r (Work.OROneRel.zeta t w') = presentRho r w := by
      rw [zeta_eq_magnusMap t, hw']
    exact h1.trans h3

/-- **The order of the class of the root is unchanged by the Magnus step.**  If the class of the
Magnus rewriting `magRewRel t u` has order exactly `l` in the Magnus base, then so does the class of
the root `u` in `G = ⟨α | r⟩`, `r = u ^ l`, because `m` is injective and
`m (magRewRel t u) = presentRho r u`. -/
theorem orderOf_of_magnusStep (t : α) (r u : FreeGroup α) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1)
    (m : MagnusBase t u l →* OneRelatorGroup r) (hm : Function.Injective m)
    (hcomp : m.comp (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t))
    (hord : orderOf (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
      (Work.OROneRel.magRewRel t u)) = l) :
    orderOf (presentRho r u) = l := by
  have hv : m (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
      (Work.OROneRel.magRewRel t u)) = presentRho r u := by
    have h1 : m (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
        (Work.OROneRel.magRewRel t u)) =
        presentRho r (Work.OROneRel.zeta t (Work.OROneRel.magRewRel t u)) := by
      have h2 := DFunLike.congr_fun hcomp (Work.OROneRel.magRewRel t u)
      simpa only [MonoidHom.comp_apply] using h2
    rw [h1, ← eq_zeta_magRewRel t u hσ]
  have hpowl : (presentRho r u) ^ l = 1 := by
    rw [← map_pow, ← hpow, presentRho_relator]
  have hne : ∀ k : ℕ, k < l → 0 < k → (presentRho r u) ^ k ≠ 1 := by
    intro k hkl hk0 hk
    have h1 : (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
        (Work.OROneRel.magRewRel t u)) ^ k = 1 := by
      apply hm
      rw [map_pow, hv, hk, map_one]
    have h2 : orderOf (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
        (Work.OROneRel.magRewRel t u)) ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hord] at h2
    exact hk0.ne' (Nat.eq_zero_of_dvd_of_lt h2 hkl)
  rw [orderOf_eq_iff (by omega : 0 < l)]
  exact ⟨hpowl, hne⟩

end Base

section Transfer

variable {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
variable {hσ : Work.OROneRel.sigma t u = 1}

/-- **The leading-level transfer with the base regularity as a hypothesis.**  Let `E` be the base
element which is the `i`-th level part of the root Fox vector up to the factor `τ ^ i`.  If
multiplication by `E` is injective on the elements supported on the Magnus base `ker (levelOf)`
(`hbase`), then the `x`-component of the root Fox vector is right regular.

The point of this wrapper is that `hE0` (which the transfer
`Work.ORLyndon.ann_rootVec_of_level_top` carries along but does not use) is *derived* here from
`hbase`: if `E = 0` then `hbase` would force `1 = 0` in `K[G]`, which is impossible. -/
theorem ann_rootVec_of_level_base (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (E : MonoidAlgebra K (OneRelatorGroup r))
    (hEbase : ∀ g ∈ E.coeff.support, levelOf t r u l hpow hσ g = 1)
    (hDecomp : levelPart t r u l hpow hσ i (rootVec K r u x) =
      E * MonoidAlgebra.of K (OneRelatorGroup r) ((presentRho r (FreeGroup.of t)) ^ i))
    (hDbound : ∀ g ∈ (rootVec K r u x).coeff.support,
      (levelOf t r u l hpow hσ g).toAdd ≤ i)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) → c * E = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 := by
  classical
  have hE0 : E ≠ 0 := by
    intro hEz
    have h1 : (1 : MonoidAlgebra K (OneRelatorGroup r)) = 0 := by
      refine hbase 1 ?_ (by rw [hEz, mul_zero])
      intro g hg
      have hsub := Finsupp.support_single_subset (a := (1 : OneRelatorGroup r)) (b := (1 : K))
      rw [MonoidAlgebra.one_def] at hg
      rw [Finset.mem_singleton.mp (hsub hg), map_one]
    exact one_ne_zero h1
  exact ann_rootVec_of_level_top t x hxt r u l hpow hσ i E hEbase hE0 hDecomp hDbound hbase b hb

/-- **The leading-level transfer for the Magnus rewriting.**  This assembles the transfer from the
chain rule (`Work.ORLyndon.levelPart_rootVec_eq_base`), the level bound
(`Work.ORLyndon.level_le_of_foxD_eq_zero`) and the base regularity for the element `E` which is the
image of the base Fox derivative `∂v/∂(x,i)`. -/
theorem ann_rootVec_of_magnusRewriting (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (hdec : ∀ j : ℤ, i < j →
      foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0)
    (hbase : ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) →
      c * MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
            (foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, i)
              (Work.OROneRel.magRewRel t u)) = 0 → c = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 := by
  have hEbase : ∀ g ∈ (MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
      (foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, i) (Work.OROneRel.magRewRel t u))).coeff.support,
      levelOf t r u l hpow hσ g = 1 :=
    levelOf_support_mapDomainRingHom_zeta t r u l hpow hσ _
  refine ann_rootVec_of_level_base t x hxt r u l hpow hσ i _ hEbase ?_
    (level_le_of_foxD_eq_zero (K := K) (t := t) (r := r) (u := u) (l := l)
      (hpow := hpow) (hσ := hσ) hxt hdec) hbase b hb
  rw [levelPart_rootVec_eq_base t x hxt r u l hpow hσ i]

end Transfer

section Assembly

variable {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
variable {hσ : Work.OROneRel.sigma t u = 1}

/-- **The base regularity in `K[G]` from the induction hypothesis at the Magnus base.**

The induction hypothesis at the Magnus base `⟨β | (magRewRel t u) ^ l⟩` gives that the base element
`∂v/∂(x,i)` (`v = magRewRel t u`) is right regular in `K` of the base.  Along the embedding `m` of the
base into `G` (with `m ∘ mk` compatible with `ζ_t` and hence with range the Magnus base
`ker (levelOf)`), this transports to the statement that multiplication by the image of `∂v/∂(x,i)` is
injective on the elements of `K[G]` supported on `ker (levelOf)` — the hypothesis `hbase` of the
leading-level transfer. -/
theorem hbase_of_ih (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (m : MagnusBase t u l →* OneRelatorGroup r) (hm : Function.Injective m)
    (hcomp : m.comp (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t))
    (hIH : ∀ c : MonoidAlgebra K (MagnusBase t u l),
      c * rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) (⟨x, hxt⟩, i) = 0 → c = 0) :
    ∀ c : MonoidAlgebra K (OneRelatorGroup r),
      (∀ g ∈ c.coeff.support, levelOf t r u l hpow hσ g = 1) →
      c * MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
            (foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, i)
              (Work.OROneRel.magRewRel t u)) = 0 → c = 0 := by
  have hcomp' : m.comp (presentRho (magRewRelPow t u l)) =
      (presentRho r).comp (Work.OROneRel.zeta t) := hcomp
  have hid : MonoidAlgebra.mapDomainRingHom K m
      (rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) (⟨x, hxt⟩, i)) =
      MonoidAlgebra.mapDomainRingHom K ((presentRho r).comp (Work.OROneRel.zeta t))
        (foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, i) (Work.OROneRel.magRewRel t u)) := by
    rw [rootVec_apply]
    simp only [presentAlg]
    change ((MonoidAlgebra.mapDomainRingHom K m).comp
        (MonoidAlgebra.mapDomainRingHom K (presentRho (magRewRelPow t u l))))
        (foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, i)
          (Work.OROneRel.magRewRel t u)) = _
    rw [← MonoidAlgebra.mapDomainRingHom_comp, hcomp']
  intro c hc hcE
  rw [← hid] at hcE
  exact base_regularity_transport m hm (levelOf t r u l hpow hσ)
    (range_eq_ker_levelOf t r u l hpow hσ m hcomp)
    (rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) (⟨x, hxt⟩, i)) hIH c hc hcE

/-- **The `x`-component of the root Fox vector is right regular** — the `(I)` half of the
exponent-sum-zero Magnus step of the Cohen--Lyndon induction. -/
theorem ann_rootVec_of_magnusStep (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpow : r = u ^ l) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (m : MagnusBase t u l →* OneRelatorGroup r) (hm : Function.Injective m)
    (hcomp : m.comp (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t))
    (hIH : ∀ q : MagnusBeta t, q ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u) →
      ∀ c : MonoidAlgebra K (MagnusBase t u l),
        c * rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) q = 0 → c = 0)
    (hocc : ((⟨x, hxt⟩, i) : MagnusBeta t) ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u))
    (hdec : ∀ j : ℤ, i < j →
      foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0)
    (b : MonoidAlgebra K (OneRelatorGroup r)) (hb : b * rootVec K r u x = 0) : b = 0 :=
  ann_rootVec_of_magnusRewriting t x hxt r u l hpow hσ i hdec
    (hbase_of_ih t x hxt r u l hpow hσ i m hm hcomp (hIH _ hocc)) b hb

/-- **The exponent-sum-zero Magnus step of the Cohen--Lyndon induction.**

Let `r = u ^ l` with `u` not a proper power and `σ_t u = 1` (exponent sum zero in `t`).  Suppose the
Magnus base `⟨β | (magRewRel t u) ^ l⟩` embeds into `G = ⟨α | r⟩` through `m` (compatibly with the
Magnus rewriting), and suppose the induction hypothesis at the Magnus base provides both the order of
the root (`hIHord`) and the right regularity of every component of its Fox vector (`hIH`).  Then the
Cohen--Lyndon independence holds for `u` in `G`. -/
theorem lyndon_independence_of_pow_eps_zero (t x : α) (hxt : x ≠ t) (r u : FreeGroup α) (l : ℕ)
    (hpos : 1 ≤ l) (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (m : MagnusBase t u l →* OneRelatorGroup r) (hm : Function.Injective m)
    (hcomp : m.comp (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t))
    (hIH : ∀ q : MagnusBeta t, q ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u) →
      ∀ c : MonoidAlgebra K (MagnusBase t u l),
        c * rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) q = 0 → c = 0)
    (hIHord : orderOf (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
      (Work.OROneRel.magRewRel t u)) = l)
    (hocc : ((⟨x, hxt⟩, i) : MagnusBeta t) ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u))
    (hdec : ∀ j : ℤ, i < j →
      foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0) :
    LyndonIndependence K r u :=
  lyndon_independence_of_rootVec_inj r u l hpos hpow
    (orderOf_of_magnusStep t r u l hpos hpow hσ m hm hcomp hIHord)
    (ann_rootVec_of_component r u x
      (ann_rootVec_of_magnusStep t x hxt r u l hpow hσ i m hm hcomp hIH hocc hdec))

end Assembly

section CanonicalMap

/-- **The canonical map from the Magnus base to `G`.**  It is the map induced on the one-relator
group `⟨β | (magRewRel t u) ^ l⟩` by the Magnus rewriting `ζ_t : (x,i) ↦ t ^ i x t ^ (-i)`, which
sends the base relator `(magRewRel t u) ^ l` to `u ^ l = r`. -/
noncomputable def magnusBaseMap (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) : MagnusBase t u l →* OneRelatorGroup r :=
  PresentedGroup.toGroup
    (f := fun q : MagnusBeta t => presentRho r (Work.OROneRel.zeta t (FreeGroup.of q)))
    (by
      have hlift : FreeGroup.lift
          (fun q : MagnusBeta t => presentRho r (Work.OROneRel.zeta t (FreeGroup.of q))) =
          (presentRho r).comp (Work.OROneRel.zeta t) := by
        refine FreeGroup.ext_hom _ _ fun q => ?_
        rw [FreeGroup.lift_apply_of]
        rfl
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [hlift]
      show presentRho r (Work.OROneRel.zeta t (Work.OROneRel.magRewRel t u ^ l)) = 1
      rw [map_pow, ← eq_zeta_magRewRel t u hσ, ← hpow, presentRho_relator])

/-- The defining property of `Work.ORLyndon.magnusBaseMap`: it is the map `mk w ↦ ζ_t(w)` on the
free group on the decorated alphabet. -/
theorem magnusBaseMap_comp (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) :
    (magnusBaseMap t r u l hpow hσ).comp
        (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t) := by
  refine FreeGroup.ext_hom _ _ fun q => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact PresentedGroup.toGroup.of _

end CanonicalMap

section Canonical

variable {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
variable {hσ : Work.OROneRel.sigma t u = 1}

/-- **The exponent-sum-zero Magnus step with the canonical Magnus base map.**  Compared with
`Work.ORLyndon.lyndon_independence_of_pow_eps_zero`, the compatibility `hcomp` is now a theorem
(`Work.ORLyndon.magnusBaseMap_comp`), so the only inputs besides the decoration bounds are

* the *injectivity* of the canonical map `⟨β | (magRewRel t u) ^ l⟩ →* G` — this is the "the Magnus
  base injects" part of the Magnus step (equivalently the Freiheitssatz input of the HNN structure);
* the induction hypothesis at the Magnus base `⟨β | (magRewRel t u) ^ l⟩`, whose root
  `magRewRel t u` has smaller norm than `u` and is not a proper power. -/
theorem lyndon_independence_of_pow_eps_zero_canonical (t x : α) (hxt : x ≠ t)
    (r u : FreeGroup α) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hσ : Work.OROneRel.sigma t u = 1) (i : ℤ)
    (hm : Function.Injective (magnusBaseMap t r u l hpow hσ))
    (hIH : ∀ q : MagnusBeta t, q ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u) →
      ∀ c : MonoidAlgebra K (MagnusBase t u l),
        c * rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) q = 0 → c = 0)
    (hIHord : orderOf (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
      (Work.OROneRel.magRewRel t u)) = l)
    (hocc : ((⟨x, hxt⟩, i) : MagnusBeta t) ∈
      Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u))
    (hdec : ∀ j : ℤ, i < j →
      foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0) :
    LyndonIndependence K r u :=
  lyndon_independence_of_pow_eps_zero t x hxt r u l hpos hpow hpp hσ i
    (magnusBaseMap t r u l hpow hσ) hm (magnusBaseMap_comp t r u l hpow hσ) hIH hIHord hocc hdec

end Canonical

section MmHi

variable {t : α} {r u : FreeGroup α} {l : ℕ} {hpow : r = u ^ l}
variable {hσ : Work.OROneRel.sigma t u = 1}

/-- **The exponent-sum-zero Magnus step, with the decoration data discharged.**

Here the level `i` is instantiated with the *largest decoration* `mmHi t u ⟨x, hxt⟩` of a letter
`x ≠ t` occurring in `u` (`Work.ORLyndon.mmHi_mem_relatorLetters`), so that the two decoration
hypotheses `hocc` and `hdec` of `Work.ORLyndon.lyndon_independence_of_pow_eps_zero` become
theorems. -/
theorem lyndon_independence_of_pow_eps_zero_of_mmHi (t : α) (r u : FreeGroup α) (l : ℕ)
    (hpos : 1 ≤ l) (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hσ : Work.OROneRel.sigma t u = 1) (x : α) (hxt : x ≠ t)
    (hx : x ∈ Work.OROneRel.relatorLetters u)
    (m : MagnusBase t u l →* OneRelatorGroup r) (hm : Function.Injective m)
    (hcomp : m.comp (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))) =
      (presentRho r).comp (Work.OROneRel.zeta t))
    (hIH : ∀ q : MagnusBeta t, q ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t u) →
      ∀ c : MonoidAlgebra K (MagnusBase t u l),
        c * rootVec K (magRewRelPow t u l) (Work.OROneRel.magRewRel t u) q = 0 → c = 0)
    (hIHord : orderOf (PresentedGroup.mk ({magRewRelPow t u l} : Set (FreeGroup (MagnusBeta t)))
      (Work.OROneRel.magRewRel t u)) = l) :
    LyndonIndependence K r u := by
  have hdec : ∀ j : ℤ, Work.OROneRel.mmHi t u ⟨x, hxt⟩ < j →
      foxD (K := K) (X := MagnusBeta t) (⟨x, hxt⟩, j) (Work.OROneRel.magRewRel t u) = 0 := by
    intro j hj
    refine foxD_eq_zero_of_notMem_relatorLetters (K := K) _ _ fun hmem => ?_
    exact absurd ((mmHi_mem_relatorLetters t u ⟨x, hxt⟩ hx).2 j hmem) (not_le.mpr hj)
  exact lyndon_independence_of_pow_eps_zero t x hxt r u l hpos hpow hpp hσ
    (Work.OROneRel.mmHi t u ⟨x, hxt⟩) m hm hcomp hIH hIHord
    (mmHi_mem_relatorLetters t u ⟨x, hxt⟩ hx).1 hdec

end MmHi

end Work.ORLyndon
