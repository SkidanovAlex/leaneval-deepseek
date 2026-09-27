import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.monoid_grothendieck
import Submission.Work.KT.sumMvN
import Submission.Work.KT.sum_mvN_assoc
import Submission.Work.KT.sum_mvN_congr
import Submission.Work.KT.rel_cancel

/-!
# `Work.KT.cls_eq_stable_mvN`

**(K2)** Two idempotent matrices have the same class in `K₀ R` if and only if they become
Murray–von Neumann equivalent after adding identity blocks.

The forward direction is the statement that `K₀ R` is the group completion of the commutative
monoid `V R` of idempotent matrices modulo *stable* Murray–von Neumann equivalence.  We build the
monoid `V R` (idempotents modulo `k2Srel`, with block sum), verify that `cls` descends to a
monoid homomorphism `k2V R → K₀ R`, and that the induced map out of the abstract group completion
`monoid_grothendieck` gives equality of classes only after stabilisation.  Cancellation of a common
idempotent block then reduces to cancellation of a *free* block (`rel_cancel`).
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-! ## Block sums of identity matrices -/

/-- `1ₖ ⊕ 1ₗ = 1_{k+l}` on the nose. -/
theorem k2_one_sum_one (R : Type) [Ring R] (k l : ℕ) :
    (Mat.one R k).sum (Mat.one R l) = Mat.one R (k + l) := by
  unfold Mat.sum Mat.one
  simp [Matrix.fromBlocks_one]

/-- `1ₖ ⊕ 1ₗ ∼ 1_{k+l}`. -/
theorem k2_mvN_one_sum_one (R : Type) [Ring R] (k l : ℕ) :
    Mat.MvN ((Mat.one R k).sum (Mat.one R l)) (Mat.one R (k + l)) := by
  rw [k2_one_sum_one R k l]
  exact Mat.mvN_refl (Mat.one_isIdem R (k + l))

/-! ## Increasing the stabilising free block -/

/-- If `p ⊕ 1ₖ ∼ q ⊕ 1ₖ` then the same holds with the stabilising block enlarged to `k + l`. -/
theorem k2_mvN_add_one_right {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem)
    {k : ℕ} (h : Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k))) (l : ℕ) :
    Mat.MvN (p.sum (Mat.one R (k + l))) (q.sum (Mat.one R (k + l))) := by
  have hok : (Mat.one R k).IsIdem := Mat.one_isIdem R k
  have hol : (Mat.one R l).IsIdem := Mat.one_isIdem R l
  have hpl : (p.sum (Mat.one R k)).IsIdem := Mat.sum_idem hp hok
  have hql : (q.sum (Mat.one R k)).IsIdem := Mat.sum_idem hq hok
  have hpkl : (p.sum (Mat.one R (k + l))).IsIdem := Mat.sum_idem hp (Mat.one_isIdem R (k + l))
  have hqkl : (q.sum (Mat.one R (k + l))).IsIdem := Mat.sum_idem hq (Mat.one_isIdem R (k + l))
  have hpll : ((p.sum (Mat.one R k)).sum (Mat.one R l)).IsIdem := Mat.sum_idem hpl hol
  have hqll : ((q.sum (Mat.one R k)).sum (Mat.one R l)).IsIdem := Mat.sum_idem hql hol
  have hpq : Mat.MvN ((p.sum (Mat.one R k)).sum (Mat.one R l))
      ((q.sum (Mat.one R k)).sum (Mat.one R l)) :=
    sum_mvN_congr R _ _ _ _ h (Mat.mvN_refl hol)
  have hpL : Mat.MvN (p.sum (Mat.one R (k + l))) ((p.sum (Mat.one R k)).sum (Mat.one R l)) := by
    have h' := sum_mvN_assoc R p (Mat.one R k) (Mat.one R l)
    rw [k2_one_sum_one R k l] at h'
    exact Mat.mvN_symm h'
  have hqL : Mat.MvN ((q.sum (Mat.one R k)).sum (Mat.one R l)) (q.sum (Mat.one R (k + l))) := by
    have h' := sum_mvN_assoc R q (Mat.one R k) (Mat.one R l)
    rw [k2_one_sum_one R k l] at h'
    exact h'
  exact Mat.mvN_trans hpkl hpll hqkl hpL (Mat.mvN_trans hpll hqll hqkl hpq hqL)

/-- Transitivity of stable Murray–von Neumann equivalence. -/
theorem k2_stabMvN_trans {a b c : Mat R} (ha : a.IsIdem) (hb : b.IsIdem) (hc : c.IsIdem)
    (k l : ℕ)
    (hk : Mat.MvN (a.sum (Mat.one R k)) (b.sum (Mat.one R k)))
    (hl : Mat.MvN (b.sum (Mat.one R l)) (c.sum (Mat.one R l))) :
    Mat.MvN (a.sum (Mat.one R (k + l))) (c.sum (Mat.one R (k + l))) := by
  have h1 := k2_mvN_add_one_right ha hb hk l
  have h2 := k2_mvN_add_one_right hb hc hl k
  rw [Nat.add_comm l k] at h2
  exact Mat.mvN_trans (Mat.sum_idem ha (Mat.one_isIdem R (k + l)))
    (Mat.sum_idem hb (Mat.one_isIdem R (k + l)))
    (Mat.sum_idem hc (Mat.one_isIdem R (k + l))) h1 h2

/-! ## The interchange law for block sums -/

/-- `(p ⊕ q) ⊕ (r ⊕ s) ∼ (p ⊕ r) ⊕ (q ⊕ s)` for idempotents. -/
theorem k2_mvN_sum4 {p q r s : Mat R}
    (hp : p.IsIdem) (hq : q.IsIdem) (hr : r.IsIdem) (hs : s.IsIdem) :
    Mat.MvN ((p.sum q).sum (r.sum s)) ((p.sum r).sum (q.sum s)) := by
  have hqr : (q.sum r).IsIdem := Mat.sum_idem hq hr
  have hrq : (r.sum q).IsIdem := Mat.sum_idem hr hq
  have hrs : (r.sum s).IsIdem := Mat.sum_idem hr hs
  have hqs : (q.sum s).IsIdem := Mat.sum_idem hq hs
  have i1 : ((p.sum q).sum (r.sum s)).IsIdem := Mat.sum_idem (Mat.sum_idem hp hq) hrs
  have i2 : (p.sum (q.sum (r.sum s))).IsIdem := Mat.sum_idem hp (Mat.sum_idem hq hrs)
  have i3 : (p.sum ((q.sum r).sum s)).IsIdem := Mat.sum_idem hp (Mat.sum_idem hqr hs)
  have i4 : (p.sum ((r.sum q).sum s)).IsIdem := Mat.sum_idem hp (Mat.sum_idem hrq hs)
  have i5 : (p.sum (r.sum (q.sum s))).IsIdem := Mat.sum_idem hp (Mat.sum_idem hr hqs)
  have i6 : ((p.sum r).sum (q.sum s)).IsIdem := Mat.sum_idem (Mat.sum_idem hp hr) hqs
  have h1 : Mat.MvN ((p.sum q).sum (r.sum s)) (p.sum (q.sum (r.sum s))) :=
    sum_mvN_assoc R p q (r.sum s)
  have h2 : Mat.MvN (p.sum (q.sum (r.sum s))) (p.sum ((q.sum r).sum s)) :=
    sum_mvN_congr R p p (q.sum (r.sum s)) ((q.sum r).sum s) (Mat.mvN_refl hp)
      (Mat.mvN_symm (sum_mvN_assoc R q r s))
  have h3 : Mat.MvN (p.sum ((q.sum r).sum s)) (p.sum ((r.sum q).sum s)) :=
    sum_mvN_congr R p p ((q.sum r).sum s) ((r.sum q).sum s) (Mat.mvN_refl hp)
      (sum_mvN_congr R (q.sum r) (r.sum q) s s (mvN_sum_comm q r) (Mat.mvN_refl hs))
  have h4 : Mat.MvN (p.sum ((r.sum q).sum s)) (p.sum (r.sum (q.sum s))) :=
    sum_mvN_congr R p p ((r.sum q).sum s) (r.sum (q.sum s)) (Mat.mvN_refl hp)
      (sum_mvN_assoc R r q s)
  have h5 : Mat.MvN (p.sum (r.sum (q.sum s))) ((p.sum r).sum (q.sum s)) :=
    Mat.mvN_symm (sum_mvN_assoc R p r (q.sum s))
  exact Mat.mvN_trans i1 i2 i6 h1
    (Mat.mvN_trans i2 i3 i6 h2
      (Mat.mvN_trans i3 i4 i6 h3
        (Mat.mvN_trans i4 i5 i6 h4 h5)))

/-- Additivity of stable Murray–von Neumann equivalence. -/
theorem k2_stabMvN_add {a a' b b' : Mat R}
    (ha : a.IsIdem) (ha' : a'.IsIdem) (hb : b.IsIdem) (hb' : b'.IsIdem) (k l : ℕ)
    (h1 : Mat.MvN (a.sum (Mat.one R k)) (a'.sum (Mat.one R k)))
    (h2 : Mat.MvN (b.sum (Mat.one R l)) (b'.sum (Mat.one R l))) :
    Mat.MvN ((a.sum b).sum (Mat.one R (k + l))) ((a'.sum b').sum (Mat.one R (k + l))) := by
  have hok : (Mat.one R k).IsIdem := Mat.one_isIdem R k
  have hol : (Mat.one R l).IsIdem := Mat.one_isIdem R l
  have iA : ((a.sum b).sum (Mat.one R (k + l))).IsIdem :=
    Mat.sum_idem (Mat.sum_idem ha hb) (Mat.one_isIdem R (k + l))
  have iB : (((a.sum (Mat.one R k)).sum (b.sum (Mat.one R l)))).IsIdem :=
    Mat.sum_idem (Mat.sum_idem ha hok) (Mat.sum_idem hb hol)
  have iC : (((a'.sum (Mat.one R k)).sum (b'.sum (Mat.one R l)))).IsIdem :=
    Mat.sum_idem (Mat.sum_idem ha' hok) (Mat.sum_idem hb' hol)
  have iD : ((a'.sum b').sum (Mat.one R (k + l))).IsIdem :=
    Mat.sum_idem (Mat.sum_idem ha' hb') (Mat.one_isIdem R (k + l))
  have h : Mat.MvN ((a.sum (Mat.one R k)).sum (b.sum (Mat.one R l)))
      ((a'.sum (Mat.one R k)).sum (b'.sum (Mat.one R l))) := sum_mvN_congr R _ _ _ _ h1 h2
  have hL : Mat.MvN ((a.sum (Mat.one R k)).sum (b.sum (Mat.one R l)))
      ((a.sum b).sum (Mat.one R (k + l))) := by
    have hh := k2_mvN_sum4 ha hok hb hol
    rw [k2_one_sum_one R k l] at hh
    exact hh
  have hR : Mat.MvN ((a'.sum (Mat.one R k)).sum (b'.sum (Mat.one R l)))
      ((a'.sum b').sum (Mat.one R (k + l))) := by
    have hh := k2_mvN_sum4 ha' hok hb' hol
    rw [k2_one_sum_one R k l] at hh
    exact hh
  exact Mat.mvN_trans iA iB iD (Mat.mvN_symm hL) (Mat.mvN_trans iB iC iD h hR)

/-! ## The commutative monoid `k2V R` of idempotents up to stable MvN -/

/-- Idempotent square matrices, as a type. -/
abbrev k2Idem (R : Type) [Ring R] : Type := {p : Mat R // p.IsIdem}

/-- Block sum of idempotents. -/
def k2idemAdd (a b : k2Idem R) : k2Idem R := ⟨a.1.sum b.1, Mat.sum_idem a.2 b.2⟩

instance k2instAddIdem : Add (k2Idem R) := ⟨k2idemAdd⟩

instance k2instZeroIdem : Zero (k2Idem R) := ⟨⟨Mat.one R 0, Mat.one_isIdem R 0⟩⟩

instance k2instSetoidIdem (R : Type) [Ring R] : Setoid (k2Idem R) where
  r a b := ∃ k : ℕ, Mat.MvN (a.1.sum (Mat.one R k)) (b.1.sum (Mat.one R k))
  iseqv := ⟨fun a => ⟨0, Mat.mvN_refl (Mat.sum_idem a.2 (Mat.one_isIdem R 0))⟩,
    fun h => by obtain ⟨k, hk⟩ := h; exact ⟨k, Mat.mvN_symm hk⟩,
    fun {a b c} h₁ h₂ => by
      obtain ⟨k, hk⟩ := h₁
      obtain ⟨l, hl⟩ := h₂
      exact ⟨k + l, k2_stabMvN_trans a.2 b.2 c.2 k l hk hl⟩⟩

/-- Idempotent matrices modulo stable Murray–von Neumann equivalence. -/
abbrev k2V (R : Type) [Ring R] : Type := Quotient (k2instSetoidIdem R)

/-- The class of a block sum, as an element of `k2V R`. -/
def k2idemAddQ (a b : k2Idem R) : k2V R := Quotient.mk (k2instSetoidIdem R) (k2idemAdd a b)

theorem k2idemAdd_lift (a₁ b₁ a₂ b₂ : k2Idem R) (h₁ : a₁ ≈ a₂) (h₂ : b₁ ≈ b₂) :
    k2idemAddQ a₁ b₁ = k2idemAddQ a₂ b₂ := by
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨l, hl⟩ := h₂
  refine Quotient.sound ⟨k + l, ?_⟩
  exact k2_stabMvN_add a₁.2 a₂.2 b₁.2 b₂.2 k l hk hl

instance k2instAddV : Add (k2V R) :=
  ⟨fun x y => Quotient.liftOn₂ x y k2idemAddQ (k2idemAdd_lift (R := R))⟩

theorem k2V_mk_add (a b : k2Idem R) :
    (Quotient.mk (k2instSetoidIdem R) a + Quotient.mk (k2instSetoidIdem R) b : k2V R) =
      Quotient.mk (k2instSetoidIdem R) (a + b) := by
  show Quotient.liftOn₂ (Quotient.mk (k2instSetoidIdem R) a) (Quotient.mk (k2instSetoidIdem R) b)
    k2idemAddQ (k2idemAdd_lift (R := R)) = Quotient.mk (k2instSetoidIdem R) (a + b)
  rw [Quotient.liftOn₂_mk]
  rfl

/-- The zero of `k2V R`. -/
def k2V_zero (R : Type) [Ring R] : k2V R := Quotient.mk (k2instSetoidIdem R) 0

instance k2instZeroV : Zero (k2V R) := ⟨k2V_zero R⟩

/-- `0 + x = x` in `k2V R`. -/
theorem k2V_zero_add (x : k2V R) : (0 : k2V R) + x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  show Quotient.mk (k2instSetoidIdem R) (0 : k2Idem R) + Quotient.mk (k2instSetoidIdem R) a
      = Quotient.mk (k2instSetoidIdem R) a
  rw [k2V_mk_add]
  refine Quotient.sound ⟨0, ?_⟩
  show Mat.MvN (((Mat.one R 0).sum a.1).sum (Mat.one R 0)) (a.1.sum (Mat.one R 0))
  have h1 : (((Mat.one R 0).sum a.1).sum (Mat.one R 0)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem (Mat.one_isIdem R 0) a.2) (Mat.one_isIdem R 0)
  have h2 : ((Mat.one R 0).sum a.1).IsIdem := Mat.sum_idem (Mat.one_isIdem R 0) a.2
  have h3 : (a.1.sum (Mat.one R 0)).IsIdem := Mat.sum_idem a.2 (Mat.one_isIdem R 0)
  exact Mat.mvN_trans h1 h2 h3 (mvN_sum_one_zero ((Mat.one R 0).sum a.1))
    (Mat.mvN_trans h2 a.2 h3 (mvN_one_zero_sum a.1) (Mat.mvN_symm (mvN_sum_one_zero a.1)))

/-- `x + 0 = x` in `k2V R`. -/
theorem k2V_add_zero (x : k2V R) : x + (0 : k2V R) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  show Quotient.mk (k2instSetoidIdem R) a + Quotient.mk (k2instSetoidIdem R) (0 : k2Idem R)
      = Quotient.mk (k2instSetoidIdem R) a
  rw [k2V_mk_add]
  refine Quotient.sound ⟨0, ?_⟩
  show Mat.MvN ((a.1.sum (Mat.one R 0)).sum (Mat.one R 0)) (a.1.sum (Mat.one R 0))
  exact mvN_sum_one_zero (a.1.sum (Mat.one R 0))

instance k2instAddCommMonoidV : AddCommMonoid (k2V R) where
  add := (· + ·)
  zero := k2V_zero R
  nsmul := nsmulRec
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    simp only [k2V_mk_add]
    refine Quotient.sound ⟨0, ?_⟩
    show Mat.MvN (((a + b).1.sum c.1).sum (Mat.one R 0)) ((a + (b + c)).1.sum (Mat.one R 0))
    have h1 : ((((a + b).1).sum c.1).sum (Mat.one R 0)).IsIdem :=
      Mat.sum_idem (Mat.sum_idem (Mat.sum_idem a.2 b.2) c.2) (Mat.one_isIdem R 0)
    have h2 : (((a + b).1).sum c.1).IsIdem := Mat.sum_idem (Mat.sum_idem a.2 b.2) c.2
    have h3 : (a.1.sum (b.1.sum c.1)).IsIdem := Mat.sum_idem a.2 (Mat.sum_idem b.2 c.2)
    have h4 : ((a.1.sum (b.1.sum c.1)).sum (Mat.one R 0)).IsIdem :=
      Mat.sum_idem h3 (Mat.one_isIdem R 0)
    exact Mat.mvN_trans h1 h2 h4 (mvN_sum_one_zero ((a.1.sum b.1).sum c.1))
      (Mat.mvN_trans h2 h3 h4 (sum_mvN_assoc R a.1 b.1 c.1)
        (Mat.mvN_symm (mvN_sum_one_zero (a.1.sum (b.1.sum c.1)))))
  zero_add := k2V_zero_add
  add_zero := k2V_add_zero
  add_comm := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    simp only [k2V_mk_add]
    refine Quotient.sound ⟨0, ?_⟩
    show Mat.MvN (((a + b).1.sum (Mat.one R 0))) (((b + a).1.sum (Mat.one R 0)))
    have h1 : (((a.1.sum b.1).sum (Mat.one R 0))).IsIdem :=
      Mat.sum_idem (Mat.sum_idem a.2 b.2) (Mat.one_isIdem R 0)
    have h2 : (a.1.sum b.1).IsIdem := Mat.sum_idem a.2 b.2
    have h3 : (b.1.sum a.1).IsIdem := Mat.sum_idem b.2 a.2
    have h4 : (((b.1.sum a.1).sum (Mat.one R 0))).IsIdem :=
      Mat.sum_idem h3 (Mat.one_isIdem R 0)
    exact Mat.mvN_trans h1 h2 h4 (mvN_sum_one_zero (a.1.sum b.1))
      (Mat.mvN_trans h2 h3 h4 (mvN_sum_comm a.1 b.1)
        (Mat.mvN_symm (mvN_sum_one_zero (b.1.sum a.1))))

/-- `k2V R` has cancellation: a common stabilising block may be cancelled. -/
theorem k2V_add_cancel (x y z : k2V R) (h : x + z = y + z) : x = y := by
  revert h
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b
  refine Quotient.inductionOn z ?_
  intro c
  intro h
  simp only [k2V_mk_add] at h ⊢
  have h' : ∃ k : ℕ, Mat.MvN (((a + c).1).sum (Mat.one R k)) (((b + c).1).sum (Mat.one R k)) :=
    Quotient.exact h
  obtain ⟨k, hk⟩ := h'
  have hk' : ∃ k : ℕ, Mat.MvN ((a.1.sum c.1).sum (Mat.one R k))
      ((b.1.sum c.1).sum (Mat.one R k)) := ⟨k, hk⟩
  obtain ⟨m, hm⟩ := rel_cancel.2 R a.1 b.1 c.1 a.2 b.2 c.2 hk'
  exact Quotient.sound ⟨m, hm⟩

/-! ## Detection: equal `K₀`-classes imply stable Murray–von Neumann equivalence -/

theorem k2_K0_detect {R : Type} [Ring R] (p q : Mat R) (hp : p.IsIdem) (hq : q.IsIdem)
    (h : cls p = cls q) :
    ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k)) := by
  classical
  obtain ⟨G, hG, f, hfadd, hfker⟩ := monoid_grothendieck (k2V R)
  let φ : Mat R → G :=
    fun m => if hm : m.IsIdem then f (Quotient.mk (k2instSetoidIdem R) ⟨m, hm⟩) else 0
  have hφ : ∀ (m : Mat R) (hm : m.IsIdem),
      φ m = f (Quotient.mk (k2instSetoidIdem R) ⟨m, hm⟩) := fun m hm => dif_pos hm
  have hφ_add : ∀ (a b : Mat R) (ha : a.IsIdem) (hb : b.IsIdem),
      φ (a.sum b) = φ a + φ b := by
    intro a b ha hb
    rw [hφ (a.sum b) (Mat.sum_idem ha hb), hφ a ha, hφ b hb, ← hfadd, k2V_mk_add]
    rfl
  have hφ_mvN : ∀ (a b : Mat R) (ha : a.IsIdem) (hb : b.IsIdem), Mat.MvN a b → φ a = φ b := by
    intro a b ha hb hmv
    rw [hφ a ha, hφ b hb, hfker]
    refine ⟨Quotient.mk (k2instSetoidIdem R) ⟨b, hb⟩, ?_⟩
    rw [k2V_mk_add, k2V_mk_add]
    refine Quotient.sound ⟨0, ?_⟩
    show Mat.MvN (((a.sum b).sum (Mat.one R 0))) (((b.sum b).sum (Mat.one R 0)))
    have h1 : ((a.sum b).sum (Mat.one R 0)).IsIdem :=
      Mat.sum_idem (Mat.sum_idem ha hb) (Mat.one_isIdem R 0)
    have h2 : (a.sum b).IsIdem := Mat.sum_idem ha hb
    have h3 : (b.sum b).IsIdem := Mat.sum_idem hb hb
    have h4 : ((b.sum b).sum (Mat.one R 0)).IsIdem :=
      Mat.sum_idem h3 (Mat.one_isIdem R 0)
    exact Mat.mvN_trans h1 h2 h4 (mvN_sum_one_zero (a.sum b))
      (Mat.mvN_trans h2 h3 h4 (sum_mvN_congr R _ _ _ _ hmv (Mat.mvN_refl hb))
        (Mat.mvN_symm (mvN_sum_one_zero (b.sum b))))
  let Φ : FreeAbelianGroup (Mat R) →+ G := FreeAbelianGroup.lift φ
  have hΦφ : ∀ m : Mat R, Φ (FreeAbelianGroup.of m) = φ m :=
    fun m => FreeAbelianGroup.lift_apply_of φ m
  have hΦ : ∀ (m : Mat R) (hm : m.IsIdem),
      Φ (FreeAbelianGroup.of m) = f (Quotient.mk (k2instSetoidIdem R) ⟨m, hm⟩) := by
    intro m hm
    rw [hΦφ m]
    exact hφ m hm
  have hvanish : K0Rel R ≤ Φ.ker := by
    rw [K0Rel, AddSubgroup.closure_le]
    rintro x ((⟨a, b, ha, hb, rfl⟩ | ⟨a, b, ha, hb, hmv, rfl⟩) | ⟨a, ha, rfl⟩)
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub]
      rw [hΦφ (a.sum b), hΦφ a, hΦφ b, hφ_add a b ha hb]
      abel
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub]
      rw [hΦφ a, hΦφ b, sub_eq_zero]
      exact hφ_mvN a b ha hb hmv
    · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker]
      rw [hΦφ a]
      exact dif_neg ha
  let Ψ : K0 R →+ G := QuotientAddGroup.lift (K0Rel R) Φ hvanish
  have hΨ : ∀ (m : Mat R) (hm : m.IsIdem),
      Ψ (cls m) = f (Quotient.mk (k2instSetoidIdem R) ⟨m, hm⟩) := by
    intro m hm
    show (QuotientAddGroup.lift (K0Rel R) Φ hvanish)
      (QuotientAddGroup.mk (FreeAbelianGroup.of m)) = _
    rw [QuotientAddGroup.lift_mk]
    exact hΦ m hm
  have hψ : Ψ (cls p) = Ψ (cls q) := by rw [h]
  rw [hΨ p hp, hΨ q hq] at hψ
  obtain ⟨c, hc⟩ := (hfker _ _).1 hψ
  have hpq : Quotient.mk (k2instSetoidIdem R) ⟨p, hp⟩ = Quotient.mk (k2instSetoidIdem R) ⟨q, hq⟩ :=
    k2V_add_cancel _ _ c hc
  exact Quotient.exact hpq

end

/-! ## The theorem -/

/-- **(K2)** Two idempotent matrices have the same class in `K₀ R` if and only if they become Murray–von Neumann equivalent after adding identity blocks.  Proof sketch: `K₀ R` is the group completion of the monoid of idempotents modulo `Mat.MvN` with `⊕`, so equal classes force `p ⊕ r ~ q ⊕ r` for some idempotent `r`, and `r ⊕ (1 - r) ~ 1`. -/
theorem cls_eq_stable_mvN {R : Type} [Ring R] (p q : Mat R) (hp : p.IsIdem) (hq : q.IsIdem) :
    cls p = cls q ↔ ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k)) := by
  constructor
  · exact k2_K0_detect p q hp hq
  · rintro ⟨k, hk⟩
    have hok : (Mat.one R k).IsIdem := Mat.one_isIdem R k
    have h1 : cls (p.sum (Mat.one R k)) = cls (q.sum (Mat.one R k)) :=
      cls_eq_of_mvN (Mat.sum_idem hp hok) (Mat.sum_idem hq hok) hk
    rw [cls_sum hp hok, cls_sum hq hok] at h1
    exact add_right_cancel h1

end Work.KT
