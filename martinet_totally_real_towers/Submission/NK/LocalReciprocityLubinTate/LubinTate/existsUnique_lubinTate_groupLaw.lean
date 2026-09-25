import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series
import Submission.NK.LocalReciprocityLubinTate.LubinTate.FormalGroup
import Submission.NK.LocalReciprocityLubinTate.LubinTate.existsUnique_lubinTate_solution

/-!
# The Lubin–Tate formal group law: existence and uniqueness

Milne, *Classical Field Theory*, Lemma I.2.11 and Proposition I.2.12 (Serre, *Local Fields*,
Ch. XV §3, Thms. 3.1–3.3): given a Lubin–Tate series `f` for `(π, q)` over `A`, there is a unique
formal group law `F` over `A` with `F ≡ X + Y (mod deg 2)`, of which `f` is an endomorphism, and
`F` is commutative.

The series `F` is the unique solution, produced by `existsUnique_lubinTate_solution`, of the
substitution equation `f(F(X,Y)) = F(f(X),f(Y))` (`IsLTEndo` below); the group-law axioms are then
obtained by applying the *same* uniqueness statement in three variables (associativity) and in two
variables with the variables swapped (commutativity).
-/

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

noncomputable section

variable {A : Type u} [CommRing A]

/-- The variable `X i` of the `n`-variable power series ring over the coefficient ring `A`, with
both the number of variables and the coefficient ring determined by the arguments (the bare
`MvPowerSeries.X` leaves the coefficient ring to be inferred). -/
abbrev mvX (A : Type u) [CommRing A] (n : ℕ) (i : Fin n) : MvPowerSeries (Fin n) A :=
  MvPowerSeries.X i

/-! ### The defining substitution equation of the group law, in `n` variables -/

/-- `IsLTEndo n f y` is the substitution identity `f(y(X)) = y(f(X₁),…,f(X_n))` of Milne's
Lemma I.2.11, for an `n`-variable series `y` (for `n = 2` it is exactly
`IsEndoSeries y f`). -/
def IsLTEndo (n : ℕ) (f : MvPowerSeries (Fin 1) A) (y : MvPowerSeries (Fin n) A) : Prop :=
  MvPowerSeries.subst ![y] f = y.subst (gSub n f)

theorem isLTEndo_iff_isEndoSeries (f : MvPowerSeries (Fin 1) A) (y : MvPowerSeries (Fin 2) A) :
    IsLTEndo 2 f y ↔ NK.LocalReciprocityLubinTate.IsEndoSeries y f := by
  unfold IsLTEndo NK.LocalReciprocityLubinTate.IsEndoSeries gSub
  constructor <;> intro h
  · rw [h]
    congr 1
    funext i
    fin_cases i <;> rfl
  · rw [h]
    congr 1
    funext i
    fin_cases i <;> rfl

/-- **The functional form of the defining equation**: if `y` satisfies the substitution identity of
Milne's Lemma I.2.11, then so does `y(a,b)` for any pair of series of positive order. -/
theorem isEndoSeries_subst_pair {φ : MvPowerSeries (Fin 2) A} {f : MvPowerSeries (Fin 1) A}
    (h : NK.LocalReciprocityLubinTate.IsEndoSeries φ f) (hφ : φ.constantCoeff = 0)
    (hf : f.constantCoeff = 0) {τ : Type*} {a b : MvPowerSeries τ A}
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    MvPowerSeries.subst ![φ.subst ![a, b]] f
      = φ.subst ![MvPowerSeries.subst ![a] f, MvPowerSeries.subst ![b] f] := by
  have hab : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries τ A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [ha, hb])
  have hφ' : MvPowerSeries.HasSubst (![φ] : Fin 1 → MvPowerSeries (Fin 2) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i; simpa using hφ)
  have hX0 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (0 : Fin 2)] : Fin 1 → MvPowerSeries (Fin 2) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i; simp)
  have hX1 : MvPowerSeries.HasSubst
      (![MvPowerSeries.X (1 : Fin 2)] : Fin 1 → MvPowerSeries (Fin 2) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i; simp)
  have hg0 : constantCoeff (MvPowerSeries.subst
      (![MvPowerSeries.X (0 : Fin 2)] : Fin 1 → MvPowerSeries (Fin 2) A) f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hX0 (fun i => by fin_cases i; simp) hf
  have hg1 : constantCoeff (MvPowerSeries.subst
      (![MvPowerSeries.X (1 : Fin 2)] : Fin 1 → MvPowerSeries (Fin 2) A) f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hX1 (fun i => by fin_cases i; simp) hf
  have hg : MvPowerSeries.HasSubst
      (![MvPowerSeries.subst (![MvPowerSeries.X (0 : Fin 2)] :
            Fin 1 → MvPowerSeries (Fin 2) A) f,
         MvPowerSeries.subst (![MvPowerSeries.X (1 : Fin 2)] :
            Fin 1 → MvPowerSeries (Fin 2) A) f] : Fin 2 → MvPowerSeries (Fin 2) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simpa [hg0, hg1])
  have hL : MvPowerSeries.subst ![φ.subst ![a, b]] f
      = MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries τ A)
          (MvPowerSeries.subst (![φ] : Fin 1 → MvPowerSeries (Fin 2) A) f) := by
    rw [MvPowerSeries.subst_comp_subst_apply hφ' hab f]
    congr 1
    funext i
    fin_cases i
    rfl
  have hXX0 : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries τ A)
      (MvPowerSeries.subst (![MvPowerSeries.X (0 : Fin 2)] :
        Fin 1 → MvPowerSeries (Fin 2) A) f) = MvPowerSeries.subst ![a] f := by
    rw [MvPowerSeries.subst_comp_subst_apply hX0 hab f]
    congr 1
    funext j
    fin_cases j
    simp only [Matrix.cons_val_fin_one]
    rw [MvPowerSeries.subst_X hab]
    simp
  have hXX1 : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries τ A)
      (MvPowerSeries.subst (![MvPowerSeries.X (1 : Fin 2)] :
        Fin 1 → MvPowerSeries (Fin 2) A) f) = MvPowerSeries.subst ![b] f := by
    rw [MvPowerSeries.subst_comp_subst_apply hX1 hab f]
    congr 1
    funext j
    fin_cases j
    simp only [Matrix.cons_val_fin_one]
    rw [MvPowerSeries.subst_X hab]
    simp
  have hR : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries τ A)
        (φ.subst ![MvPowerSeries.subst (![MvPowerSeries.X (0 : Fin 2)] :
              Fin 1 → MvPowerSeries (Fin 2) A) f,
            MvPowerSeries.subst (![MvPowerSeries.X (1 : Fin 2)] :
              Fin 1 → MvPowerSeries (Fin 2) A) f])
      = φ.subst ![MvPowerSeries.subst ![a] f, MvPowerSeries.subst ![b] f] := by
    rw [MvPowerSeries.subst_comp_subst_apply hg hab φ]
    have hfam : (fun s : Fin 2 => MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries τ A)
        (![MvPowerSeries.subst (![MvPowerSeries.X (0 : Fin 2)] :
              Fin 1 → MvPowerSeries (Fin 2) A) f,
           MvPowerSeries.subst (![MvPowerSeries.X (1 : Fin 2)] :
              Fin 1 → MvPowerSeries (Fin 2) A) f] s))
        = ![MvPowerSeries.subst ![a] f, MvPowerSeries.subst ![b] f] := by
      funext i
      fin_cases i
      · simpa using hXX0
      · simpa using hXX1
    rw [hfam]
  rw [hL, h, hR]

/-! ### Congruence modulo total degree two, and the group-law axioms of Mathlib's `FormalGroup` -/

theorem congruentModDegTwo_iff_orderGe_two {σ : Type*} {f g : MvPowerSeries σ A} :
    NK.LocalReciprocityLubinTate.CongruentModDegTwo f g ↔ OrderGe 2 (f - g) :=
  (orderGe_sub_iff (k := 2)).symm

theorem congruentModDegTwo_iff_coeff_le_one {σ : Type*} {f g : MvPowerSeries σ A} :
    NK.LocalReciprocityLubinTate.CongruentModDegTwo f g ↔
      ∀ s : σ →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s f = MvPowerSeries.coeff s g := by
  rw [congruentModDegTwo_iff_orderGe_two, orderGe_sub_iff]
  exact ⟨fun h s hs => h s (by omega), fun h s hs => h s (by omega)⟩

/-- Every Mathlib formal group law is congruent to `X + Y` modulo total degree two: this is
exactly the content of the three fields `zero_constantCoeff`, `lin_coeff_X`, `lin_coeff_Y`. -/
theorem congruentModDegTwo_formalGroup (F : FormalGroup A) :
    NK.LocalReciprocityLubinTate.CongruentModDegTwo (F : MvPowerSeries (Fin 2) A)
      (MvPowerSeries.X 0 + MvPowerSeries.X 1) := by
  intro s hs
  have hdeg : s.degree = s 0 + s 1 := by
    rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ s.support) (fun i _ hi => by
      simpa [Finsupp.mem_support_iff] using hi)]
    rw [Fin.sum_univ_two]
  have h0 : s 0 ≤ 1 := by omega
  have h1 : s 1 ≤ 1 := by omega
  interval_cases h : s 0 <;> interval_cases h' : s 1
  · have hs0 : s = 0 := by ext i; fin_cases i <;> simp [h, h']
    subst hs0
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.zero_constantCoeff]
  · have hs0 : s = Finsupp.single 1 1 := by ext i; fin_cases i <;> simp [h, h']
    rw [hs0, F.lin_coeff_Y]
    simp [MvPowerSeries.coeff_index_single_X]
  · have hs0 : s = Finsupp.single 0 1 := by ext i; fin_cases i <;> simp [h, h']
    rw [hs0, F.lin_coeff_X]
    simp [MvPowerSeries.coeff_index_single_X]
  · omega

/-- Substituting series of positive order into a series vanishing below degree `κ` again vanishes
below degree `κ`. -/
theorem orderGe_subst_pos {ι : Type*} [Finite ι] {τ : Type*} {q : MvPowerSeries ι A}
    {a : ι → MvPowerSeries τ A} {κ : ℕ} (hκ : 1 ≤ κ) (hq : OrderGe κ q)
    (ha : ∀ i, OrderGe 1 (a i)) : OrderGe κ (MvPowerSeries.subst a q) := by
  have hb : ∀ i, OrderGe 1 ((0 : ι → MvPowerSeries τ A) i) := fun i => orderGe_zero 1
  have hab : ∀ i, OrderGe 1 (a i - (0 : ι → MvPowerSeries τ A) i) := by
    intro i; simpa using ha i
  have h := OrderGe.subst_sub (A := A) (k := 1) (κ := κ) le_rfl hκ ha hb hab hq
  have hzero : MvPowerSeries.subst (0 : ι → MvPowerSeries τ A) q = 0 :=
    MvPowerSeries.subst_zero_of_constantCoeff_zero (OrderGe.constantCoeff (hq.mono hκ))
  simpa [hzero] using h

/-- The variable `X i` has positive order. -/
theorem orderGe_one_X {σ : Type*} (i : σ) :
    OrderGe 1 (MvPowerSeries.X i : MvPowerSeries σ A) :=
  OrderGe.of_constantCoeff (by simp)

/-- The composition law for substituting into a two-variable series. -/
theorem subst_comp_pair {τ υ : Type*} {q : MvPowerSeries (Fin 2) A} {a b : MvPowerSeries τ A}
    {c : τ → MvPowerSeries υ A} (hab : MvPowerSeries.HasSubst ![a, b])
    (hc : MvPowerSeries.HasSubst c) :
    MvPowerSeries.subst c (q.subst ![a, b])
      = q.subst ![MvPowerSeries.subst c a, MvPowerSeries.subst c b] := by
  rw [MvPowerSeries.subst_comp_subst_apply hab hc q]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The constant coefficient of `g(a,b)` vanishes when `g` and `a`, `b` have vanishing constant
coefficient. -/
theorem constantCoeff_subst_pair {τ : Type*} {g : MvPowerSeries (Fin 2) A}
    (hg : g.constantCoeff = 0) {a b : MvPowerSeries τ A} (ha : a.constantCoeff = 0)
    (hb : b.constantCoeff = 0) : (g.subst ![a, b]).constantCoeff = 0 := by
  have hfam : ∀ i : Fin 2, constantCoeff ((![a, b] : Fin 2 → MvPowerSeries τ A) i) = 0 :=
    fun i => by fin_cases i <;> simp [ha, hb]
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hfam) hfam hg

/-- The decomposition `q(a,b) = (q - (X + Y))(a,b) + (a + b)` of a two-variable substitution along
its linear part. -/
theorem subst_pair_eq_subst_sub_linear {τ : Type*} {a b : MvPowerSeries τ A}
    (hab : MvPowerSeries.HasSubst ![a, b]) (q : MvPowerSeries (Fin 2) A) :
    (q - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst ![a, b] + (a + b) = q.subst ![a, b] := by
  rw [MvPowerSeries.subst_sub hab, MvPowerSeries.subst_add hab,
     MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ### The associativity and commutativity congruences -/

/-- The linear-part congruence for the left-associated iterate `φ(φ(X,Y),Z)`. -/
theorem congruentModDegTwo_assoc_left {φ : MvPowerSeries (Fin 2) A} (hφ0 : φ.constantCoeff = 0)
    (hR : OrderGe 2 (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1))) :
    NK.LocalReciprocityLubinTate.CongruentModDegTwo
      (φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2])
      (mvX A 3 0 + mvX A 3 1 + mvX A 3 2) := by
  rw [congruentModDegTwo_iff_orderGe_two]
  have hX : ∀ i : Fin 3, OrderGe 1 (mvX A 3 i) := fun i => orderGe_one_X i
  have hA0 : (φ.subst ![mvX A 3 0, mvX A 3 1]).constantCoeff = 0 :=
    constantCoeff_subst_pair hφ0 (by simp) (by simp)
  have hHasA : MvPowerSeries.HasSubst
      (![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2] :
        Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA0])
  have hHasX : MvPowerSeries.HasSubst
      (![mvX A 3 0, mvX A 3 1] : Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)
  have h1 : φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]
        + (φ.subst ![mvX A 3 0, mvX A 3 1] + mvX A 3 2) :=
    (subst_pair_eq_subst_sub_linear hHasA φ).symm
  have h2 : φ.subst ![mvX A 3 0, mvX A 3 1]
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![mvX A 3 0, mvX A 3 1]
        + (mvX A 3 0 + mvX A 3 1) :=
    (subst_pair_eq_subst_sub_linear hHasX φ).symm
  have hgoal : φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]
        - (mvX A 3 0 + mvX A 3 1 + mvX A 3 2)
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]
        + (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
            ![mvX A 3 0, mvX A 3 1] := by
    rw [h1, h2]
    ring
  rw [hgoal]
  have hAlin : OrderGe 1 (φ.subst ![mvX A 3 0, mvX A 3 1]) :=
    orderGe_subst_pos (κ := 1) le_rfl (OrderGe.of_constantCoeff hφ0)
      (fun i => by fin_cases i <;> simp [hX])
  refine (orderGe_subst_pos (κ := 2) (by norm_num) hR (fun i => ?_)).add
    (orderGe_subst_pos (κ := 2) (by norm_num) hR (fun i => ?_))
  · fin_cases i
    · simpa using hAlin
    · simpa using hX (2 : Fin 3)
  · fin_cases i
    · simpa using hX (0 : Fin 3)
    · simpa using hX (1 : Fin 3)

/-- The linear-part congruence for the right-associated iterate `φ(X,φ(Y,Z))`. -/
theorem congruentModDegTwo_assoc_right {φ : MvPowerSeries (Fin 2) A} (hφ0 : φ.constantCoeff = 0)
    (hR : OrderGe 2 (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1))) :
    NK.LocalReciprocityLubinTate.CongruentModDegTwo
      (φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]])
      (mvX A 3 0 + mvX A 3 1 + mvX A 3 2) := by
  rw [congruentModDegTwo_iff_orderGe_two]
  have hX : ∀ i : Fin 3, OrderGe 1 (mvX A 3 i) := fun i => orderGe_one_X i
  have hB0 : (φ.subst ![mvX A 3 1, mvX A 3 2]).constantCoeff = 0 :=
    constantCoeff_subst_pair hφ0 (by simp) (by simp)
  have hHasB : MvPowerSeries.HasSubst
      (![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]] :
        Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hB0])
  have hHasX : MvPowerSeries.HasSubst
      (![mvX A 3 1, mvX A 3 2] : Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)
  have h1 : φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]
        + (mvX A 3 0 + φ.subst ![mvX A 3 1, mvX A 3 2]) :=
    (subst_pair_eq_subst_sub_linear hHasB φ).symm
  have h2 : φ.subst ![mvX A 3 1, mvX A 3 2]
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![mvX A 3 1, mvX A 3 2]
        + (mvX A 3 1 + mvX A 3 2) :=
    (subst_pair_eq_subst_sub_linear hHasX φ).symm
  have hgoal : φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]
        - (mvX A 3 0 + mvX A 3 1 + mvX A 3 2)
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]
        + (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
            ![mvX A 3 1, mvX A 3 2] := by
    rw [h1, h2]
    ring
  rw [hgoal]
  have hBlin : OrderGe 1 (φ.subst ![mvX A 3 1, mvX A 3 2]) :=
    orderGe_subst_pos (κ := 1) le_rfl (OrderGe.of_constantCoeff hφ0)
      (fun i => by fin_cases i <;> simp [hX])
  refine (orderGe_subst_pos (κ := 2) (by norm_num) hR (fun i => ?_)).add
    (orderGe_subst_pos (κ := 2) (by norm_num) hR (fun i => ?_))
  · fin_cases i
    · simpa using hX (0 : Fin 3)
    · simpa using hBlin
  · fin_cases i
    · simpa using hX (1 : Fin 3)
    · simpa using hX (2 : Fin 3)

/-- The linear-part congruence for the swapped law `φ(Y,X)`. -/
theorem congruentModDegTwo_swap {φ : MvPowerSeries (Fin 2) A}
    (hR : OrderGe 2 (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1))) :
    NK.LocalReciprocityLubinTate.CongruentModDegTwo
      (φ.subst ![mvX A 2 1, mvX A 2 0]) (mvX A 2 0 + mvX A 2 1) := by
  rw [congruentModDegTwo_iff_orderGe_two]
  have hX : ∀ i : Fin 2, OrderGe 1 (mvX A 2 i) := fun i => orderGe_one_X i
  have hHas : MvPowerSeries.HasSubst
      (![mvX A 2 1, mvX A 2 0] : Fin 2 → MvPowerSeries (Fin 2) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)
  have h1 : φ.subst ![mvX A 2 1, mvX A 2 0]
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![mvX A 2 1, mvX A 2 0] + (mvX A 2 1 + mvX A 2 0) :=
    (subst_pair_eq_subst_sub_linear hHas φ).symm
  have hgoal : φ.subst ![mvX A 2 1, mvX A 2 0]
        - (mvX A 2 0 + mvX A 2 1)
      = (φ - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).subst
          ![mvX A 2 1, mvX A 2 0] := by
    rw [h1]
    ring
  rw [hgoal]
  exact orderGe_subst_pos (κ := 2) (by norm_num) hR (fun i => by
    fin_cases i
    · simpa using hX (1 : Fin 2)
    · simpa using hX (0 : Fin 2))

/-! ### The defining equations of the three substituted series -/

/-- `f(φ(φ(X,Y),Z)) = φ(φ(fX,fY),fZ)`. -/
theorem isLTEndo_assoc_left {φ : MvPowerSeries (Fin 2) A} {f : MvPowerSeries (Fin 1) A}
    (hy : NK.LocalReciprocityLubinTate.IsEndoSeries φ f) (hφ0 : φ.constantCoeff = 0)
    (hf0 : f.constantCoeff = 0) :
    IsLTEndo 3 f (φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]) := by
  unfold IsLTEndo
  have hX0 : (mvX A 3 0).constantCoeff = 0 := by simp
  have hX1 : (mvX A 3 1).constantCoeff = 0 := by simp
  have hX2 : (mvX A 3 2).constantCoeff = 0 := by simp
  have hA0 : (φ.subst ![mvX A 3 0, mvX A 3 1]).constantCoeff = 0 :=
    constantCoeff_subst_pair hφ0 hX0 hX1
  have h3 : MvPowerSeries.HasSubst (gSub 3 f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => gSub_constantCoeff hf0 i)
  have hA2 : MvPowerSeries.HasSubst
      (![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2] :
        Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA0])
  have hXp : MvPowerSeries.HasSubst
      (![mvX A 3 0, mvX A 3 1] : Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)
  rw [isEndoSeries_subst_pair hy hφ0 hf0 hA0 hX2]
  rw [isEndoSeries_subst_pair hy hφ0 hf0 hX0 hX1]
  rw [subst_comp_pair hA2 h3]
  rw [subst_comp_pair hXp h3]
  simp only [MvPowerSeries.subst_X h3]
  rfl

/-- `f(φ(X,φ(Y,Z))) = φ(fX,φ(fY,fZ))`. -/
theorem isLTEndo_assoc_right {φ : MvPowerSeries (Fin 2) A} {f : MvPowerSeries (Fin 1) A}
    (hy : NK.LocalReciprocityLubinTate.IsEndoSeries φ f) (hφ0 : φ.constantCoeff = 0)
    (hf0 : f.constantCoeff = 0) :
    IsLTEndo 3 f (φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]) := by
  unfold IsLTEndo
  have hX0 : (mvX A 3 0).constantCoeff = 0 := by simp
  have hX1 : (mvX A 3 1).constantCoeff = 0 := by simp
  have hX2 : (mvX A 3 2).constantCoeff = 0 := by simp
  have hB0 : (φ.subst ![mvX A 3 1, mvX A 3 2]).constantCoeff = 0 :=
    constantCoeff_subst_pair hφ0 hX1 hX2
  have h3 : MvPowerSeries.HasSubst (gSub 3 f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => gSub_constantCoeff hf0 i)
  have hB2 : MvPowerSeries.HasSubst
      (![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]] :
        Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hB0])
  have hXp : MvPowerSeries.HasSubst
      (![mvX A 3 1, mvX A 3 2] : Fin 2 → MvPowerSeries (Fin 3) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)
  rw [isEndoSeries_subst_pair hy hφ0 hf0 hX0 hB0]
  rw [isEndoSeries_subst_pair hy hφ0 hf0 hX1 hX2]
  rw [subst_comp_pair hB2 h3]
  rw [subst_comp_pair hXp h3]
  simp only [MvPowerSeries.subst_X h3]
  rfl

/-- `f(φ(Y,X)) = φ(fY,fX)`. -/
theorem isLTEndo_swap {φ : MvPowerSeries (Fin 2) A} {f : MvPowerSeries (Fin 1) A}
    (hy : NK.LocalReciprocityLubinTate.IsEndoSeries φ f) (hφ0 : φ.constantCoeff = 0)
    (hf0 : f.constantCoeff = 0) :
    IsLTEndo 2 f (φ.subst ![mvX A 2 1, mvX A 2 0]) := by
  unfold IsLTEndo
  have hX0 : (mvX A 2 0).constantCoeff = 0 := by simp
  have hX1 : (mvX A 2 1).constantCoeff = 0 := by simp
  have h2 : MvPowerSeries.HasSubst (gSub 2 f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => gSub_constantCoeff hf0 i)
  have hXp : MvPowerSeries.HasSubst
      (![mvX A 2 1, mvX A 2 0] : Fin 2 → MvPowerSeries (Fin 2) A) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp)
  rw [isEndoSeries_subst_pair hy hφ0 hf0 hX1 hX0]
  rw [subst_comp_pair hXp h2]
  simp only [MvPowerSeries.subst_X h2]
  rfl

/-! ### The theorem -/

/-- The condition `φ₁.constantCoeff = 0`, `φ₁` of degree `≥ 2` vanishing, for the linear forms
`X + Y` and `X + Y + Z`. -/
theorem coeff_X_eq_zero_of_two_le {σ : Type*} [DecidableEq σ] (i : σ) {s : σ →₀ ℕ}
    (hs : 2 ≤ s.degree) :
    MvPowerSeries.coeff s (MvPowerSeries.X i : MvPowerSeries σ A) = 0 := by
  rw [MvPowerSeries.coeff_X]
  have hne : s ≠ Finsupp.single i 1 := by
    intro h
    rw [h, Finsupp.degree_single] at hs
    omega
  simp [hne]

theorem existsUnique_lubinTate_groupLaw {A : Type u} [CommRing A] {π : A} {q : ℕ}
    (hπ : NK.LocalReciprocityLubinTate.IsLubinTateCoeff π q)
    (hpow : NK.LocalReciprocityLubinTate.IsFrobeniusPower π q)
    {f : MvPowerSeries (Fin 1) A} (hf : NK.LocalReciprocityLubinTate.IsLubinTateSeries π q f) :
    ∃! F : FormalGroup A,
      NK.LocalReciprocityLubinTate.CongruentModDegTwo (F : MvPowerSeries (Fin 2) A)
          (MvPowerSeries.X 0 + MvPowerSeries.X 1) ∧
      NK.LocalReciprocityLubinTate.IsEndoSeries (F : MvPowerSeries (Fin 2) A) f ∧
      FormalGroup.IsComm F := by
  have hf0 : f.constantCoeff = 0 := hf.constantCoeff
  -- ## the two-variable solution
  have h2cond : (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 :
        MvPowerSeries (Fin 2) A).constantCoeff = 0 ∧
      ∀ s : Fin 2 →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s
        (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) = 0 := by
    constructor
    · simp
    · intro s hs
      rw [map_add, coeff_X_eq_zero_of_two_le (A := A) (0 : Fin 2) hs,
        coeff_X_eq_zero_of_two_le (A := A) (1 : Fin 2) hs, add_zero]
  obtain ⟨φ, ⟨hlin, heq⟩, huniq⟩ := existsUnique_lubinTate_solution (n := 2) hπ hpow hf hf
    (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) h2cond
  have hφ0 : φ.constantCoeff = 0 := by
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hlin 0 (by simp)
  have hR : OrderGe 2 (φ - (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1)) :=
    (congruentModDegTwo_iff_orderGe_two).mp
      ((congruentModDegTwo_iff_coeff_le_one).mpr hlin)
  have hendo : NK.LocalReciprocityLubinTate.IsEndoSeries φ f := by
    rw [← isLTEndo_iff_isEndoSeries f φ]
    unfold IsLTEndo
    rw [heq]
    rfl
  -- ## the three-variable solution
  have h3cond : (mvX A 3 0 + mvX A 3 1 + mvX A 3 2 :
        MvPowerSeries (Fin 3) A).constantCoeff = 0 ∧
      ∀ s : Fin 3 →₀ ℕ, 2 ≤ s.degree → MvPowerSeries.coeff s
        (mvX A 3 0 + mvX A 3 1 + mvX A 3 2) = 0 := by
    constructor
    · simp
    · intro s hs
      rw [map_add, map_add, coeff_X_eq_zero_of_two_le (A := A) (0 : Fin 3) hs,
        coeff_X_eq_zero_of_two_le (A := A) (1 : Fin 3) hs,
        coeff_X_eq_zero_of_two_le (A := A) (2 : Fin 3) hs, add_zero, add_zero]
  obtain ⟨ψ, ⟨hψlin, hψeq⟩, hψuniq⟩ := existsUnique_lubinTate_solution (n := 3) hπ hpow hf hf
    (mvX A 3 0 + mvX A 3 1 + mvX A 3 2) h3cond
  -- ## associativity: both associations solve the same three-variable problem
  have hΦlin : ∀ s : Fin 3 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s
        (φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2])
      = MvPowerSeries.coeff s (mvX A 3 0 + mvX A 3 1 + mvX A 3 2) :=
    (congruentModDegTwo_iff_coeff_le_one).mp (congruentModDegTwo_assoc_left hφ0 hR)
  have hΦeq : MvPowerSeries.subst
        ![φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]] f
      = (φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]).subst
          (fun i => MvPowerSeries.subst ![MvPowerSeries.X i] f) :=
    isLTEndo_assoc_left hendo hφ0 hf0
  have hΨlin : ∀ s : Fin 3 →₀ ℕ, s.degree ≤ 1 → MvPowerSeries.coeff s
        (φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]])
      = MvPowerSeries.coeff s (mvX A 3 0 + mvX A 3 1 + mvX A 3 2) :=
    (congruentModDegTwo_iff_coeff_le_one).mp (congruentModDegTwo_assoc_right hφ0 hR)
  have hΨeq : MvPowerSeries.subst
        ![φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]] f
      = (φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]]).subst
          (fun i => MvPowerSeries.subst ![MvPowerSeries.X i] f) :=
    isLTEndo_assoc_right hendo hφ0 hf0
  have hassoc : φ.subst ![φ.subst ![mvX A 3 0, mvX A 3 1], mvX A 3 2]
      = φ.subst ![mvX A 3 0, φ.subst ![mvX A 3 1, mvX A 3 2]] :=
    (hψuniq _ ⟨hΦlin, hΦeq⟩).trans (hψuniq _ ⟨hΨlin, hΨeq⟩).symm
  -- ## commutativity
  have hGlin : ∀ s : Fin 2 →₀ ℕ, s.degree ≤ 1 →
      MvPowerSeries.coeff s (φ.subst ![mvX A 2 1, mvX A 2 0])
        = MvPowerSeries.coeff s (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) :=
    (congruentModDegTwo_iff_coeff_le_one).mp (congruentModDegTwo_swap hR)
  have hGeq : MvPowerSeries.subst ![φ.subst ![mvX A 2 1, mvX A 2 0]] f
      = (φ.subst ![mvX A 2 1, mvX A 2 0]).subst
          (fun i => MvPowerSeries.subst ![MvPowerSeries.X i] f) :=
    isLTEndo_swap hendo hφ0 hf0
  have hGφ : φ.subst ![mvX A 2 1, mvX A 2 0] = φ := huniq _ ⟨hGlin, hGeq⟩
  -- ## the formal group law
  have hlinX : φ.coeff (Finsupp.single (0 : Fin 2) 1) = 1 := by
    have h := hlin (Finsupp.single (0 : Fin 2) 1) (by simp [Finsupp.degree_single])
    simpa [MvPowerSeries.coeff_index_single_X] using h
  have hlinY : φ.coeff (Finsupp.single (1 : Fin 2) 1) = 1 := by
    have h := hlin (Finsupp.single (1 : Fin 2) 1) (by simp [Finsupp.degree_single])
    simpa [MvPowerSeries.coeff_index_single_X] using h
  let F : FormalGroup A :=
    { toPowerSeries := φ
      zero_constantCoeff := hφ0
      lin_coeff_X := hlinX
      lin_coeff_Y := hlinY
      assoc := hassoc }
  refine ⟨F, ⟨congruentModDegTwo_formalGroup F, hendo, ⟨hGφ.symm⟩⟩, ?_⟩
  intro y hy
  obtain ⟨hycong, hyendo, -⟩ := hy
  have hylin : ∀ s : Fin 2 →₀ ℕ, s.degree ≤ 1 →
      MvPowerSeries.coeff s (y : MvPowerSeries (Fin 2) A)
        = MvPowerSeries.coeff s (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) :=
    (congruentModDegTwo_iff_coeff_le_one).mp hycong
  have hyeq : MvPowerSeries.subst ![(y : MvPowerSeries (Fin 2) A)] f
      = (y : MvPowerSeries (Fin 2) A).subst (gSub 2 f) :=
    (isLTEndo_iff_isEndoSeries f (y : MvPowerSeries (Fin 2) A)).mpr hyendo
  exact FormalGroup.ext (huniq _ ⟨hylin, hyeq⟩)

end

end NK.LocalReciprocityLubinTate.LubinTate
