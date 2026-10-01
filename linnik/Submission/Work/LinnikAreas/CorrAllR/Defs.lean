import Mathlib

/-!
# Correlation sums for the general-`r` Burgess moment bound

This module collects the definitions shared by the pieces of the proof of

`Work.LinnikAreas.moment_cubefree_all_r`

i.e. Heath-Brown, *Burgess's Bounds for Character Sums* (arXiv:1203.5219), Lemma 2 (ii)
under condition (i): for a **cube-free** modulus `q`, a primitive non-trivial `χ` and all
`H ≤ q`,

`∑_{m<q} ‖∑_{h ∈ (m, m+H]} χ h‖ ^ (2r) ≪_r q^ε (q H^r + H^(2r) √q)`.

The proof expands the `2r`-th power and reduces everything to **correlation sums**

`corrSumV n χ r v = ∑_{x : ZMod n} χ (∏_{l} (x + v_l)) · conj (χ (∏_{l} (x + v_{r+l})))`

for a `2r`-tuple of shifts `v`.  For cube-free `n` and a shift index `i` whose value `v i`
occurs only once, the correlation is bounded by
`(2r)^(ω n) √n · ∏_{j ≠ i} gcd (n, |v i - v j|)`; this is the general-`r` form of
`Commons.NumberTheory.DirichletCharacter.charCorrelation6_cubefree_global`.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas

/-- The combined shift vector `(a 0, …, a (r-1), b 0, …, b (r-1))` of two `r`-tuples. -/
def combShift {r : ℕ} (a b : Fin r → ℕ) : Fin (r + r) → ℕ := Fin.append a b

@[simp] lemma combShift_castAdd {r : ℕ} (a b : Fin r → ℕ) (l : Fin r) :
    combShift a b (Fin.castAdd r l) = a l := Fin.append_left a b l

@[simp] lemma combShift_natAdd {r : ℕ} (a b : Fin r → ℕ) (l : Fin r) :
    combShift a b (Fin.natAdd r l) = b l := Fin.append_right a b l

lemma combShift_split {r : ℕ} (w : Fin (r + r) → ℕ) :
    combShift (fun l : Fin r => w (Fin.castAdd r l)) (fun l : Fin r => w (Fin.natAdd r l)) = w := by
  funext i
  refine Fin.addCases (motive := fun i => combShift (fun l : Fin r => w (Fin.castAdd r l))
    (fun l : Fin r => w (Fin.natAdd r l)) i = w i) (fun l => ?_) (fun l => ?_) i
  · rw [combShift_castAdd]
  · rw [combShift_natAdd]

lemma combShift_injective {r : ℕ} :
    Function.Injective (fun p : (Fin r → ℕ) × (Fin r → ℕ) => combShift p.1 p.2) := by
  intro p q h
  have h1 : ∀ l : Fin r, p.1 l = q.1 l := by
    intro l
    have := congrFun h (Fin.castAdd r l)
    simpa only [combShift, Fin.append_left] using this
  have h2 : ∀ l : Fin r, p.2 l = q.2 l := by
    intro l
    have := congrFun h (Fin.natAdd r l)
    simpa only [combShift, Fin.append_right] using this
  exact Prod.ext (funext h1) (funext h2)

/-- The **correlation sum** of a Dirichlet character `χ` mod `n` over a pair of `r`-tuples of
shifts: `corrSum n χ r a b = ∑_x χ (∏_l (x + a l)) · conj (χ (∏_l (x + b l)))`. -/
noncomputable def corrSum (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (r : ℕ)
    (a b : Fin r → ℕ) : ℂ :=
  ∑ x : ZMod n, χ (∏ l : Fin r, (x + (a l : ZMod n)))
    * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (b l : ZMod n))))

/-- The **correlation sum** of `χ` mod `n` over a single `2r`-tuple of shifts:
`corrSumV n χ r v = ∑_x χ (∏_{l<r} (x + v_l)) · conj (χ (∏_{l<r} (x + v_{r+l})))`. -/
noncomputable def corrSumV (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (r : ℕ)
    (v : Fin (r + r) → ℕ) : ℂ :=
  ∑ x : ZMod n, χ (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod n)))
    * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod n))))

@[simp] lemma corrSumV_combShift {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (r : ℕ)
    (a b : Fin r → ℕ) : corrSumV n χ r (combShift a b) = corrSum n χ r a b := by
  simp only [corrSumV, corrSum, combShift_castAdd, combShift_natAdd]

/-- Trivial bound: the correlation sum is at most the number of terms. -/
lemma corrSumV_norm_le_card (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) (r : ℕ)
    (v : Fin (r + r) → ℕ) : ‖corrSumV n χ r v‖ ≤ (n : ℝ) := by
  calc ‖corrSumV n χ r v‖
      ≤ ∑ x : ZMod n, ‖χ (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod n)))
          * (starRingEnd ℂ) (χ (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod n))))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x : ZMod n, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        rw [norm_mul, Complex.norm_conj]
        have h1 := DirichletCharacter.norm_le_one χ
          (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod n)))
        have h2 := DirichletCharacter.norm_le_one χ
          (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod n)))
        nlinarith [norm_nonneg (χ (∏ l : Fin r, (x + (v (Fin.castAdd r l) : ZMod n)))),
          norm_nonneg (χ (∏ l : Fin r, (x + (v (Fin.natAdd r l) : ZMod n))))]
    _ = (n : ℝ) := by simp [Finset.sum_const, ZMod.card]

/-- The `i`-th entry of the shift tuple is **unique modulo `p`**. -/
def IsUniqModV (p : ℕ) {r : ℕ} (v : Fin (r + r) → ℕ) (i : Fin (r + r)) : Prop :=
  ∀ j : Fin (r + r), j ≠ i → v j % p ≠ v i % p

/-- The split-tuple form of `IsUniqModV`. -/
def IsUniqMod (p : ℕ) {r : ℕ} (a b : Fin r → ℕ) (i : Fin (r + r)) : Prop :=
  IsUniqModV p (combShift a b) i

instance decidableIsUniqModV {r : ℕ} (p : ℕ) (v : Fin (r + r) → ℕ) (i : Fin (r + r)) :
    Decidable (IsUniqModV p v i) := by
  unfold IsUniqModV; infer_instance

/-- The `gcd`-weight `∏_{j ≠ i} gcd (n, |v i - v j|)` attached to a shift index `i`. -/
noncomputable def gcdWeightV (n : ℕ) {r : ℕ} (v : Fin (r + r) → ℕ) (i : Fin (r + r)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, ((Nat.gcd n (((v i : ℤ) - (v j : ℤ)).natAbs) : ℕ) : ℝ)

lemma gcdWeightV_nonneg (n : ℕ) {r : ℕ} (v : Fin (r + r) → ℕ) (i : Fin (r + r)) :
    0 ≤ gcdWeightV n v i := Finset.prod_nonneg fun j _ => Nat.cast_nonneg _

/-- The split-tuple form of `gcdWeightV`. -/
noncomputable def gcdWeight (n : ℕ) {r : ℕ} (a b : Fin r → ℕ) (i : Fin (r + r)) : ℝ :=
  gcdWeightV n (combShift a b) i

/-- The reindexing equivalence `(f, g) ↦ (f 0, …, f (r-1), g 0, …, g (r-1))`. -/
noncomputable def pairEquivR (H r : ℕ) :
    ((Fin r → Fin H) × (Fin r → Fin H)) ≃ (Fin (r + r) → Fin H) where
  toFun p := Fin.append p.1 p.2
  invFun w := (fun l => w (Fin.castAdd r l), fun l => w (Fin.natAdd r l))
  left_inv p := by
    obtain ⟨f, g⟩ := p
    refine Prod.ext ?_ ?_
    · funext l
      show Fin.append f g (Fin.castAdd r l) = f l
      rw [Fin.append_left]
    · funext l
      show Fin.append f g (Fin.natAdd r l) = g l
      rw [Fin.append_right]
  right_inv w := by
    funext i
    refine Fin.addCases (motive := fun i =>
      Fin.append (fun l : Fin r => w (Fin.castAdd r l))
        (fun l : Fin r => w (Fin.natAdd r l)) i = w i) (fun l => ?_) (fun l => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]

@[simp] lemma pairEquivR_apply (H r : ℕ) (p : (Fin r → Fin H) × (Fin r → Fin H)) :
    pairEquivR H r p = Fin.append p.1 p.2 := rfl

@[simp] lemma pairEquivR_symm_fst (H r : ℕ) (w : Fin (r + r) → Fin H) (l : Fin r) :
    ((pairEquivR H r).symm w).1 l = w (Fin.castAdd r l) := rfl

@[simp] lemma pairEquivR_symm_snd (H r : ℕ) (w : Fin (r + r) → Fin H) (l : Fin r) :
    ((pairEquivR H r).symm w).2 l = w (Fin.natAdd r l) := rfl

/-- The shifts `v i = w i + 1` attached to a tuple `w` of summation indices. -/
noncomputable def pairVecH {H r : ℕ} (w : Fin (r + r) → Fin H) : Fin (r + r) → ℕ :=
  fun i => (w i : ℕ) + 1

/-- The combined vector of *shift values* `(f 0 + 1, …, f (r-1) + 1, g 0 + 1, …, g (r-1) + 1)`
attached to a pair of tuples of summation indices. -/
noncomputable def pairVec {H r : ℕ} (f g : Fin r → Fin H) : Fin (r + r) → ℕ :=
  combShift (fun l => (f l : ℕ) + 1) (fun l => (g l : ℕ) + 1)

lemma pairVec_castAdd {H r : ℕ} (f g : Fin r → Fin H) (l : Fin r) :
    pairVec f g (Fin.castAdd r l) = (f l : ℕ) + 1 := combShift_castAdd _ _ l

lemma pairVec_natAdd {H r : ℕ} (f g : Fin r → Fin H) (l : Fin r) :
    pairVec f g (Fin.natAdd r l) = (g l : ℕ) + 1 := combShift_natAdd _ _ l

lemma pairVecH_eq_iff {H r : ℕ} (w : Fin (r + r) → Fin H) (j i : Fin (r + r)) :
    pairVecH w j = pairVecH w i ↔ w j = w i := by
  constructor
  · intro h
    have h2 : ((w j : ℕ) + 1) = ((w i : ℕ) + 1) := h
    exact Fin.ext (by omega)
  · intro h
    simp only [pairVecH, h]

lemma pairVec_eq_pairVecH (H r : ℕ) (f g : Fin r → Fin H) :
    pairVec f g = pairVecH (pairEquivR H r (f, g)) := by
  funext i
  refine Fin.addCases (motive := fun i => pairVec f g i = pairVecH (pairEquivR H r (f, g)) i)
    (fun l => ?_) (fun l => ?_) i
  · rw [pairVec_castAdd, pairEquivR_apply]
    simp only [pairVecH, Fin.append_left]
  · rw [pairVec_natAdd, pairEquivR_apply]
    simp only [pairVecH, Fin.append_right]

/-- Some entry of the combined value tuple `pairVec f g` is **unique**. -/
def HasUniqIdx {H r : ℕ} (f g : Fin r → Fin H) : Prop :=
  ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → pairVec f g j ≠ pairVec f g i

/-- The corresponding condition on the reindexed tuple `w = (f, g)`. -/
def WHasUniqIdx {H r : ℕ} (w : Fin (r + r) → Fin H) : Prop :=
  ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → w j ≠ w i

lemma whasUniqIdx_iff_pairVecH {H r : ℕ} (w : Fin (r + r) → Fin H) :
    WHasUniqIdx w ↔
      ∃ i : Fin (r + r), ∀ j : Fin (r + r), j ≠ i → pairVecH w j ≠ pairVecH w i := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j hj hjj => hi j hj ?_⟩
    have h2 : ((w j : ℕ) + 1) = ((w i : ℕ) + 1) := hjj
    exact Fin.ext (by omega)
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j hj hjj => hi j hj ?_⟩
    simp only [pairVecH, hjj]

lemma hasUniqIdx_iff (H r : ℕ) (f g : Fin r → Fin H) :
    HasUniqIdx f g ↔ WHasUniqIdx (pairEquivR H r (f, g)) := by
  have hvv : pairVec f g = pairVecH (pairEquivR H r (f, g)) := pairVec_eq_pairVecH H r f g
  unfold HasUniqIdx WHasUniqIdx
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j hj => ?_⟩
    intro hcon
    exact hi j hj (by rw [hvv]; exact (pairVecH_eq_iff _ _ _).mpr hcon)
  · rintro ⟨i, hi⟩
    refine ⟨i, fun j hj => ?_⟩
    intro hcon
    exact hi j hj (by rw [hvv] at hcon; exact (pairVecH_eq_iff _ _ _).mp hcon)

instance decidableWHasUniqIdx {H r : ℕ} (w : Fin (r + r) → Fin H) : Decidable (WHasUniqIdx w) := by
  unfold WHasUniqIdx; infer_instance

noncomputable instance decidableHasUniqIdx {H r : ℕ} (f g : Fin r → Fin H) :
    Decidable (HasUniqIdx f g) := by
  unfold HasUniqIdx; infer_instance

/-- `Ww q w i = ∏_{j ≠ i} (if w j = w i then 0 else gcd (q, |w j + 1 - (w i + 1)|))`, the
`gcd`-weight of a single combined tuple `w` (in the `Fin H`-valued representation). -/
noncomputable def Ww (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (i : Fin (r + r)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (if w j = w i then 0 else (Nat.gcd q (((pairVecH w j : ℤ) - (pairVecH w i : ℤ)).natAbs) : ℝ))

lemma Ww_nonneg (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (i : Fin (r + r)) :
    0 ≤ Ww q w i := by
  refine Finset.prod_nonneg fun j _ => ?_
  by_cases h : w j = w i
  · rw [if_pos h]
  · rw [if_neg h]; positivity

/-- For a tuple whose `i`-th entry is unique, the `Fin H`-version of the `gcd`-weight agrees
with `gcdWeightV`. -/
lemma gcdWeightV_pairVecH_eq_Ww (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (i : Fin (r + r))
    (huniq : ∀ j : Fin (r + r), j ≠ i → w j ≠ w i) :
    gcdWeightV q (pairVecH w) i = Ww q w i := by
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
  have hne : w j ≠ w i := huniq j hjne
  rw [if_neg hne]
  congr 1
  rw [show (((pairVecH w i : ℤ)) - ((pairVecH w j : ℤ)))
      = -(((pairVecH w j : ℤ)) - ((pairVecH w i : ℤ))) by ring, Int.natAbs_neg]

end Work.LinnikAreas
