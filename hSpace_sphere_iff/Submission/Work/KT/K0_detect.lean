import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.monoid_grothendieck
import Submission.Work.KT.sumMvN
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.stabMvN

/-!
# `Work.KT.K0_detect`

If two idempotent matrices have the same class in the algebraic `K₀` of a ring `R`
(`Work.KT.K0`, defined as in `Submission/Work/KT/Defs.lean`), then they are *stably*
Murray–von Neumann equivalent: `p ⊕ 1ₖ ∼ q ⊕ 1ₖ` for some `k`.

The mathematical content is that `K₀ R` is the group completion of the commutative monoid of
idempotent matrices modulo stable Murray–von Neumann equivalence, so that the kernel of the
group-completion map is exactly the stable relation.  The proof below builds that monoid (`V R`),
transports the relations of `K0Rel` into it, and applies the abstract group-completion lemma
`monoid_grothendieck`.
-/

namespace Work.KT

open Matrix

noncomputable section

variable {R : Type} [Ring R]

/-! ## The Murray–von Neumann calculus of block sums

Thin wrappers with implicit arguments around the block-sum calculus proved in
`Submission/Work/KT/sumMvN.lean`, `Submission/Work/KT/stabMvN.lean` and
`Submission/Work/KT/rel_cancel.lean`. -/

theorem w_sum_congr {p q p' q' : Mat R} (h1 : Mat.MvN p p') (h2 : Mat.MvN q q') :
    Mat.MvN (p.sum q) (p'.sum q') := sumMvN.1 R p q p' q' h1 h2

theorem w_sum_comm (p q : Mat R) : Mat.MvN (p.sum q) (q.sum p) := sumMvN.2.1 R p q

theorem w_sum_assoc (p q r : Mat R) : Mat.MvN ((p.sum q).sum r) (p.sum (q.sum r)) :=
  sumMvN.2.2.1 R p q r

theorem w_sum_one_zero_right (p : Mat R) : Mat.MvN (p.sum (Mat.one R 0)) p :=
  sumMvN.2.2.2.1 R p

theorem w_sum_one_zero_left (p : Mat R) : Mat.MvN ((Mat.one R 0).sum p) p :=
  sumMvN.2.2.2.2 R p

theorem w_stab_trans {a b c : Mat R} (ha : a.IsIdem) (hb : b.IsIdem) (hc : c.IsIdem)
    (k l : ℕ) (hk : Mat.MvN (a.sum (Mat.one R k)) (b.sum (Mat.one R k)))
    (hl : Mat.MvN (b.sum (Mat.one R l)) (c.sum (Mat.one R l))) :
    Mat.MvN (a.sum (Mat.one R (k + l))) (c.sum (Mat.one R (k + l))) :=
  stabMvN.1 R a b c ha hb hc k l hk hl

theorem w_stab_add {p q p' q' : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) (hp' : p'.IsIdem)
    (hq' : q'.IsIdem) (k l : ℕ) (h1 : Mat.MvN (p.sum (Mat.one R k)) (p'.sum (Mat.one R k)))
    (h2 : Mat.MvN (q.sum (Mat.one R l)) (q'.sum (Mat.one R l))) :
    Mat.MvN ((p.sum q).sum (Mat.one R (k + l))) ((p'.sum q').sum (Mat.one R (k + l))) :=
  stabMvN.2 R p p' q q' hp hp' hq hq' k l h1 h2

/-! ## Stable Murray–von Neumann equivalence -/

theorem Mat.one_idem (k : ℕ) : (Mat.one R k).IsIdem := by
  unfold Mat.IsIdem Mat.one
  simp

/-- `Srel p q`: `p` and `q` become Murray–von Neumann equivalent after adjoining a trivial
`1ₖ` block. -/
def Srel (p q : Mat R) : Prop :=
  ∃ k : ℕ, Mat.MvN (p.sum (Mat.one R k)) (q.sum (Mat.one R k))

theorem Srel_refl {p : Mat R} (hp : p.IsIdem) : Srel p p :=
  ⟨0, Mat.mvN_refl (Mat.sum_idem hp (Mat.one_idem (R := R) 0))⟩

theorem Srel_symm {p q : Mat R} (h : Srel p q) : Srel q p := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, Mat.mvN_symm hk⟩

theorem Srel_trans {p q r : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) (hr : r.IsIdem)
    (hpq : Srel p q) (hqr : Srel q r) : Srel p r := by
  obtain ⟨k, hk⟩ := hpq
  obtain ⟨l, hl⟩ := hqr
  exact ⟨k + l, w_stab_trans hp hq hr k l hk hl⟩

theorem Srel_add {a a' b b' : Mat R} (h1 : Srel a a') (h2 : Srel b b')
    (ha : a.IsIdem) (ha' : a'.IsIdem) (hb : b.IsIdem) (hb' : b'.IsIdem) :
    Srel (a.sum b) (a'.sum b') := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  exact ⟨k + l, w_stab_add ha hb ha' hb' k l hk hl⟩

theorem Srel_comm {p q : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) : Srel (p.sum q) (q.sum p) := by
  refine ⟨0, ?_⟩
  have h1 : ((p.sum q).sum (Mat.one R 0)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem hp hq) (Mat.one_idem (R := R) 0)
  have h2 : (p.sum q).IsIdem := Mat.sum_idem hp hq
  have h3 : (q.sum p).IsIdem := Mat.sum_idem hq hp
  have h4 : ((q.sum p).sum (Mat.one R 0)).IsIdem :=
    Mat.sum_idem h3 (Mat.one_idem (R := R) 0)
  exact Mat.mvN_trans h1 h2 h4 (w_sum_one_zero_right (p.sum q))
    (Mat.mvN_trans h2 h3 h4 (w_sum_comm p q)
      (Mat.mvN_symm (w_sum_one_zero_right (q.sum p))))

theorem Srel_assoc {p q r : Mat R} (hp : p.IsIdem) (hq : q.IsIdem) (hr : r.IsIdem) :
    Srel ((p.sum q).sum r) (p.sum (q.sum r)) := by
  refine ⟨0, ?_⟩
  have h1 : (((p.sum q).sum r).sum (Mat.one R 0)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem (Mat.sum_idem hp hq) hr) (Mat.one_idem (R := R) 0)
  have h2 : ((p.sum q).sum r).IsIdem := Mat.sum_idem (Mat.sum_idem hp hq) hr
  have h3 : (p.sum (q.sum r)).IsIdem := Mat.sum_idem hp (Mat.sum_idem hq hr)
  have h4 : ((p.sum (q.sum r)).sum (Mat.one R 0)).IsIdem :=
    Mat.sum_idem h3 (Mat.one_idem (R := R) 0)
  exact Mat.mvN_trans h1 h2 h4 (w_sum_one_zero_right ((p.sum q).sum r))
    (Mat.mvN_trans h2 h3 h4 (w_sum_assoc p q r)
      (Mat.mvN_symm (w_sum_one_zero_right (p.sum (q.sum r)))))

theorem Srel_zero_add {p : Mat R} (hp : p.IsIdem) : Srel ((Mat.one R 0).sum p) p := by
  refine ⟨0, ?_⟩
  have h1 : (((Mat.one R 0).sum p).sum (Mat.one R 0)).IsIdem :=
    Mat.sum_idem (Mat.sum_idem (Mat.one_idem (R := R) 0) hp) (Mat.one_idem (R := R) 0)
  have h2 : ((Mat.one R 0).sum p).IsIdem := Mat.sum_idem (Mat.one_idem (R := R) 0) hp
  have h3 : (p.sum (Mat.one R 0)).IsIdem := Mat.sum_idem hp (Mat.one_idem (R := R) 0)
  exact Mat.mvN_trans h1 h2 h3 (w_sum_one_zero_right ((Mat.one R 0).sum p))
    (Mat.mvN_trans h2 hp h3 (w_sum_one_zero_left p)
      (Mat.mvN_symm (w_sum_one_zero_right p)))

theorem Srel_add_zero {p : Mat R} (hp : p.IsIdem) : Srel (p.sum (Mat.one R 0)) p :=
  ⟨0, w_sum_one_zero_right (p.sum (Mat.one R 0))⟩

/-! ## The commutative monoid `V R` of idempotents up to stable MvN -/

/-- Idempotent square matrices, as a type. -/
abbrev Idem (R : Type) [Ring R] : Type := {p : Mat R // p.IsIdem}

/-- Block sum of idempotents. -/
def idemAdd (a b : Idem R) : Idem R := ⟨a.1.sum b.1, Mat.sum_idem a.2 b.2⟩

instance instAddIdem : Add (Idem R) := ⟨idemAdd⟩

instance instZeroIdem : Zero (Idem R) := ⟨⟨Mat.one R 0, Mat.one_idem (R := R) 0⟩⟩

instance instSetoidIdem (R : Type) [Ring R] : Setoid (Idem R) where
  r a b := Srel a.1 b.1
  iseqv := ⟨fun a => Srel_refl a.2, fun h => Srel_symm h,
    fun {a b c} h₁ h₂ => Srel_trans a.2 b.2 c.2 h₁ h₂⟩

/-- Idempotent matrices modulo stable Murray–von Neumann equivalence. -/
abbrev V (R : Type) [Ring R] : Type := Quotient (instSetoidIdem R)

/-- The class of a block sum, as an element of `V R`. -/
def idemAddQ (a b : Idem R) : V R := Quotient.mk (instSetoidIdem R) (idemAdd a b)

theorem idemAdd_lift (a₁ b₁ a₂ b₂ : Idem R) (h₁ : a₁ ≈ a₂) (h₂ : b₁ ≈ b₂) :
    idemAddQ a₁ b₁ = idemAddQ a₂ b₂ :=
  Quotient.sound (Srel_add h₁ h₂ a₁.2 a₂.2 b₁.2 b₂.2)

instance instAddV : Add (V R) :=
  ⟨fun x y => Quotient.liftOn₂ x y idemAddQ (idemAdd_lift (R := R))⟩

theorem V_mk_add (a b : Idem R) :
    (Quotient.mk (instSetoidIdem R) a + Quotient.mk (instSetoidIdem R) b : V R) =
      Quotient.mk (instSetoidIdem R) (a + b) := by
  show Quotient.liftOn₂ (Quotient.mk (instSetoidIdem R) a) (Quotient.mk (instSetoidIdem R) b)
    idemAddQ (idemAdd_lift (R := R)) = Quotient.mk (instSetoidIdem R) (a + b)
  rw [Quotient.liftOn₂_mk]
  rfl

/-- The zero of `V R`. -/
def V_zero (R : Type) [Ring R] : V R := Quotient.mk (instSetoidIdem R) 0

instance instZeroV : Zero (V R) := ⟨V_zero R⟩

/-- `0 + x = x` in `V R`. -/
theorem V_zero_add (x : V R) : (0 : V R) + x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  show Quotient.mk (instSetoidIdem R) (0 : Idem R) + Quotient.mk (instSetoidIdem R) a
      = Quotient.mk (instSetoidIdem R) a
  rw [V_mk_add]
  exact Quotient.sound (Srel_zero_add a.2)

/-- `x + 0 = x` in `V R`. -/
theorem V_add_zero (x : V R) : x + (0 : V R) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  show Quotient.mk (instSetoidIdem R) a + Quotient.mk (instSetoidIdem R) (0 : Idem R)
      = Quotient.mk (instSetoidIdem R) a
  rw [V_mk_add]
  exact Quotient.sound (Srel_add_zero a.2)

instance instAddCommMonoidV : AddCommMonoid (V R) where
  add := (· + ·)
  zero := V_zero R
  nsmul := nsmulRec
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    simp only [V_mk_add]
    exact Quotient.sound (Srel_assoc a.2 b.2 c.2)
  zero_add := V_zero_add
  add_zero := V_add_zero
  add_comm := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    simp only [V_mk_add]
    exact Quotient.sound (Srel_comm a.2 b.2)

/-- `V R` has cancellation: a common stabilising block may be cancelled. -/
theorem V_add_cancel (x y z : V R) (h : x + z = y + z) : x = y := by
  revert h
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b
  refine Quotient.inductionOn z ?_
  intro c
  intro h
  simp only [V_mk_add] at h ⊢
  have h' : Srel (a + c).1 (b + c).1 := Quotient.exact h
  obtain ⟨k, hk⟩ := h'
  have hcancel := rel_cancel.2 R a.1 b.1 c.1 a.2 b.2 c.2
  have hk' : ∃ k : ℕ, Mat.MvN ((a.1.sum c.1).sum (Mat.one R k))
      ((b.1.sum c.1).sum (Mat.one R k)) := ⟨k, hk⟩
  obtain ⟨m, hm⟩ := hcancel hk'
  exact Quotient.sound ⟨m, hm⟩

/-! ## Detection: equal `K₀`-classes imply stable Murray–von Neumann equivalence -/

/-- **Detection.** Two idempotent matrices with the same class in `K₀ R` are stably
Murray–von Neumann equivalent.

Proof.  Let `V R` be the idempotents modulo stable `MvN` (`Srel`); block sum makes it a commutative
monoid, and it has cancellation (add the complementary idempotent
`⟨n, 1 - e⟩`, cf. `Work.KT.rel_cancel`).  By the group completion `monoid_grothendieck` there are
an abelian group `G` and an additive `f : V R → G` with `f a = f b ↔ ∃ c, a + c = b + c`.
Sending an idempotent `m` to `f ⟦m⟧` and a non-idempotent to `0` gives `φ : Mat R → G` which is
additive on block sums and constant on `MvN`-equivalent idempotents; hence
`FreeAbelianGroup.lift φ` vanishes on all three families of generators of `K0Rel` and descends to
`Ψ : K₀ R →+ G` with `Ψ (cls m) = f ⟦m⟧` for idempotent `m`.  If `cls p = cls q`, then
`f ⟦p⟧ = f ⟦q⟧`, so `⟦p⟧ + c = ⟦q⟧ + c` for some `c`, and cancellation gives `⟦p⟧ = ⟦q⟧`, i.e.
precisely `∃ k, MvN (p ⊕ 1ₖ) (q ⊕ 1ₖ)`. -/
theorem K0_detect {R : Type} [Ring R] (p q : Work.KT.Mat R) (hp : p.IsIdem) (hq : q.IsIdem)
    (h : Work.KT.cls p = Work.KT.cls q) :
    ∃ k : ℕ, Work.KT.Mat.MvN (p.sum (Work.KT.Mat.one R k)) (q.sum (Work.KT.Mat.one R k)) := by
  classical
  -- group completion of the monoid `V R`
  obtain ⟨G, hG, f, hfadd, hfker⟩ := monoid_grothendieck (V R)
  -- the map on generators: an idempotent is sent to its class in `V R`
  let φ : Mat R → G :=
    fun m => if hm : m.IsIdem then f (Quotient.mk (instSetoidIdem R) ⟨m, hm⟩) else 0
  have hφ : ∀ (m : Mat R) (hm : m.IsIdem),
      φ m = f (Quotient.mk (instSetoidIdem R) ⟨m, hm⟩) := fun m hm => dif_pos hm
  have hφ_add : ∀ (a b : Mat R) (ha : a.IsIdem) (hb : b.IsIdem),
      φ (a.sum b) = φ a + φ b := by
    intro a b ha hb
    rw [hφ (a.sum b) (Mat.sum_idem ha hb), hφ a ha, hφ b hb, ← hfadd, V_mk_add]
    rfl
  have hφ_mvN : ∀ (a b : Mat R) (ha : a.IsIdem) (hb : b.IsIdem), Mat.MvN a b → φ a = φ b := by
    intro a b ha hb hmv
    rw [hφ a ha, hφ b hb, hfker]
    refine ⟨Quotient.mk (instSetoidIdem R) ⟨b, hb⟩, ?_⟩
    rw [V_mk_add, V_mk_add]
    refine Quotient.sound ⟨0, ?_⟩
    have h1 : ((a.sum b).sum (Mat.one R 0)).IsIdem :=
      Mat.sum_idem (Mat.sum_idem ha hb) (Mat.one_idem (R := R) 0)
    have h2 : (a.sum b).IsIdem := Mat.sum_idem ha hb
    have h3 : (b.sum b).IsIdem := Mat.sum_idem hb hb
    have h4 : ((b.sum b).sum (Mat.one R 0)).IsIdem :=
      Mat.sum_idem h3 (Mat.one_idem (R := R) 0)
    exact Mat.mvN_trans h1 h2 h4 (w_sum_one_zero_right (a.sum b))
      (Mat.mvN_trans h2 h3 h4 (w_sum_congr hmv (Mat.mvN_refl hb))
        (Mat.mvN_symm (w_sum_one_zero_right (b.sum b))))
  -- the induced map on the free abelian group
  let Φ : FreeAbelianGroup (Mat R) →+ G := FreeAbelianGroup.lift φ
  have hΦφ : ∀ m : Mat R, Φ (FreeAbelianGroup.of m) = φ m :=
    fun m => FreeAbelianGroup.lift_apply_of φ m
  have hΦ : ∀ (m : Mat R) (hm : m.IsIdem),
      Φ (FreeAbelianGroup.of m) = f (Quotient.mk (instSetoidIdem R) ⟨m, hm⟩) := by
    intro m hm
    rw [hΦφ m]
    exact hφ m hm
  -- it vanishes on the relations defining `K₀`
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
  -- so it descends to `K₀`
  let Ψ : K0 R →+ G := QuotientAddGroup.lift (K0Rel R) Φ hvanish
  have hΨ : ∀ (m : Mat R) (hm : m.IsIdem),
      Ψ (cls m) = f (Quotient.mk (instSetoidIdem R) ⟨m, hm⟩) := by
    intro m hm
    show (QuotientAddGroup.lift (K0Rel R) Φ hvanish)
      (QuotientAddGroup.mk (FreeAbelianGroup.of m)) = _
    rw [QuotientAddGroup.lift_mk]
    exact hΦ m hm
  have hψ : Ψ (cls p) = Ψ (cls q) := by rw [h]
  rw [hΨ p hp, hΨ q hq] at hψ
  obtain ⟨c, hc⟩ := (hfker _ _).1 hψ
  have hpq : Quotient.mk (instSetoidIdem R) ⟨p, hp⟩ = Quotient.mk (instSetoidIdem R) ⟨q, hq⟩ :=
    V_add_cancel _ _ c hc
  exact Quotient.exact hpq

end

end Work.KT
