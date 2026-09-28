import Mathlib
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.isPrimGen_prodEquivPi_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The `-κ`-moment of `σ(·;∏ᵢ Qᵢ)` factorises over the CRT components

The Chinese remainder theorem identifies `ZMod (∏ᵢ Qᵢ)` with `∏ᵢ ZMod (Qᵢ)`; under it, primitive
coefficient vectors (and primitive zeroes of `f_a`) correspond to tuples of primitive objects, so
the density `σ` factorises and the sum
`∑_{a primitive mod ∏ᵢ Qᵢ} σ(a;∏ᵢ Qᵢ)^{-κ}` splits as the product of the individual sums.
-/

open Finset

namespace Work.HP.NA

/-- `fev` is natural: it is a polynomial expression in the coefficients and in the point. -/
private theorem fev_natural {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d n : ℕ)
    (a : Work.HP.Mon d n → R) (x : Fin (n + 1) → R) :
    fev d n (fun m => φ (a m)) (fun j => φ (x j)) = φ (fev d n a x) := by
  unfold fev
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul]
  congr 1
  unfold Work.HP.veronese
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]

/-- `σ` written as a `Nat.card` divided by the normalising factor. -/
private theorem sigQ_eq_card (d n q : ℕ) (a : Work.HP.Mon d n → ZMod q) :
    sigQ d n q a
      = (Nat.card {b : Fin (n + 1) → ZMod q // IsPrimGen q b ∧ fev d n a b = 0} : ℝ)
          / (q : ℝ) ^ n := by
  have hset : ({b : Fin (n + 1) → ZMod q | Ideal.span (Set.range b) = ⊤ ∧ fev d n a b = 0} : Set _)
      = {b : Fin (n + 1) → ZMod q | IsPrimGen q b ∧ fev d n a b = 0} := by
    ext b; exact Iff.rfl
  have h : Nat.card {b : Fin (n + 1) → ZMod q // IsPrimGen q b ∧ fev d n a b = 0}
      = ({b : Fin (n + 1) → ZMod q | IsPrimGen q b ∧ fev d n a b = 0} : Set _).ncard :=
    Nat.card_coe_set_eq _
  rw [sigQ, hset, h]

/-- `fev a b = 0` if and only if every CRT component vanishes. -/
private theorem fev_zero_iff_castHom {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → ℕ)
    [∀ i, NeZero (Q i)] (hQ : Pairwise (Function.onFun Nat.Coprime Q)) (d n : ℕ)
    (a : Work.HP.Mon d n → ZMod (∏ i, Q i)) (b : Fin (n + 1) → ZMod (∏ i, Q i)) :
    fev d n a b = 0 ↔
      ∀ i, fev d n (fun m => ZMod.castHom (dvd_prod_of_mem Q (mem_univ i)) (ZMod (Q i)) (a m))
        (fun j => ZMod.castHom (dvd_prod_of_mem Q (mem_univ i)) (ZMod (Q i)) (b j)) = 0 := by
  constructor
  · intro h i
    have h1 := fev_natural (ZMod.castHom (dvd_prod_of_mem Q (mem_univ i)) (ZMod (Q i))) d n a b
    rw [h, map_zero] at h1
    exact h1
  · intro h
    have h2 : (ZMod.prodEquivPi Q hQ) (fev d n a b) = 0 := by
      funext i
      rw [ZMod.prodEquivPi_apply]
      have h1 := fev_natural (ZMod.castHom (dvd_prod_of_mem Q (mem_univ i)) (ZMod (Q i))) d n a b
      rw [← h1]
      exact h i
    exact (ZMod.prodEquivPi Q hQ).map_eq_zero_iff.mp h2

/-- The number of primitive `b` with `fev d n a b = 0` factorises over the CRT components. -/
private theorem natCard_fev_prim_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → ℕ)
    [∀ i, NeZero (Q i)] [NeZero (∏ i, Q i)] (hQ : Pairwise (Function.onFun Nat.Coprime Q))
    (d n : ℕ) (a : Work.HP.Mon d n → ZMod (∏ i, Q i)) :
    Nat.card {b : Fin (n + 1) → ZMod (∏ i, Q i) // IsPrimGen (∏ i, Q i) b ∧ fev d n a b = 0}
      = ∏ i, Nat.card {b : Fin (n + 1) → ZMod (Q i) //
          IsPrimGen (Q i) b ∧ fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i) b = 0} := by
  classical
  let V : (Fin (n + 1) → ZMod (∏ i, Q i)) → (∀ i, Fin (n + 1) → ZMod (Q i)) :=
    fun b i j => ZMod.prodEquivPi Q hQ (b j) i
  let W : (∀ i, Fin (n + 1) → ZMod (Q i)) → (Fin (n + 1) → ZMod (∏ i, Q i)) :=
    fun x j => (ZMod.prodEquivPi Q hQ).symm (fun i => x i j)
  have hVW : ∀ x, V (W x) = x := by
    intro x; funext i j
    exact congrFun (RingEquiv.apply_symm_apply (ZMod.prodEquivPi Q hQ) (fun i => x i j)) i
  have hWV : ∀ b, W (V b) = b := by
    intro b; funext j
    exact RingEquiv.symm_apply_apply (ZMod.prodEquivPi Q hQ) (b j)
  have hp : ∀ b : Fin (n + 1) → ZMod (∏ i, Q i), IsPrimGen (∏ i, Q i) b ↔
      ∀ i, IsPrimGen (Q i) (fun j => ZMod.prodEquivPi Q hQ (b j) i) :=
    fun b => isPrimGen_prodEquivPi_iff Q hQ b
  have hf : ∀ b : Fin (n + 1) → ZMod (∏ i, Q i), fev d n a b = 0 ↔
      ∀ i, fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i)
        (fun j => ZMod.prodEquivPi Q hQ (b j) i) = 0 := by
    intro b
    rw [fev_zero_iff_castHom Q hQ d n a b]
    refine forall_congr' fun i => ?_
    simp only [ZMod.prodEquivPi_apply]
  have hW : ∀ (x : (∀ i, Fin (n + 1) → ZMod (Q i))) (i : ι),
      (fun j => ZMod.prodEquivPi Q hQ (W x j) i) = x i := fun x i => congrFun (hVW x) i
  have hbij : {b : Fin (n + 1) → ZMod (∏ i, Q i) // IsPrimGen (∏ i, Q i) b ∧ fev d n a b = 0} ≃
      {x : (∀ i, Fin (n + 1) → ZMod (Q i)) //
        ∀ i, IsPrimGen (Q i) (x i) ∧
          fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i) (x i) = 0} :=
  { toFun := fun b => ⟨V b.1, fun i => ⟨(hp b.1).mp b.2.1 i, (hf b.1).mp b.2.2 i⟩⟩
    invFun := fun x =>
      ⟨W x.1, (hp (W x.1)).mpr (fun i => by rw [hW x.1 i]; exact (x.2 i).1),
        (hf (W x.1)).mpr (fun i => by rw [hW x.1 i]; exact (x.2 i).2)⟩
    left_inv := fun b => Subtype.ext (hWV b.1)
    right_inv := fun x => Subtype.ext (hVW x.1) }
  calc Nat.card {b : Fin (n + 1) → ZMod (∏ i, Q i) // IsPrimGen (∏ i, Q i) b ∧ fev d n a b = 0}
      = Nat.card {x : (∀ i, Fin (n + 1) → ZMod (Q i)) //
          ∀ i, IsPrimGen (Q i) (x i) ∧
            fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i) (x i) = 0} :=
        Nat.card_congr hbij
    _ = Nat.card ((i : ι) → {b : Fin (n + 1) → ZMod (Q i) //
          IsPrimGen (Q i) b ∧ fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i) b = 0}) :=
        Nat.card_congr (Equiv.subtypePiEquivPi
          (β := fun i => Fin (n + 1) → ZMod (Q i))
          (p := fun i b => IsPrimGen (Q i) b ∧
            fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i) b = 0))
    _ = ∏ i, Nat.card {b : Fin (n + 1) → ZMod (Q i) //
          IsPrimGen (Q i) b ∧ fev d n (fun m => ZMod.prodEquivPi Q hQ (a m) i) b = 0} :=
        Nat.card_pi

/-- CRT multiplicativity of the density `σ`. -/
private theorem sigQ_prod_crt {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → ℕ)
    [∀ i, NeZero (Q i)] [NeZero (∏ i, Q i)] (hQ : Pairwise (Function.onFun Nat.Coprime Q))
    (d n : ℕ) (a : Work.HP.Mon d n → ZMod (∏ i, Q i)) :
    sigQ d n (∏ i, Q i) a
      = ∏ i, sigQ d n (Q i) (fun m => ZMod.prodEquivPi Q hQ (a m) i) := by
  classical
  simp_rw [sigQ_eq_card]
  rw [natCard_fev_prim_prod Q hQ d n a]
  push_cast
  rw [← Finset.prod_pow]
  rw [Finset.prod_div_distrib]

/-- `(∏_{i∈s} f i) ^ (-κ) = ∏_{i∈s} (f i) ^ (-κ)` for a nonnegative `f`. -/
private theorem prod_rpow_neg {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (κ : ℝ) : (∏ i ∈ s, f i) ^ (-κ) = ∏ i ∈ s, f i ^ (-κ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Real.mul_rpow (hf a) (Finset.prod_nonneg fun i _ => hf i), ih]

/-- `σ` is nonnegative (it is a density). -/
private theorem sigQ_nonnegative (d n q : ℕ) (a : Work.HP.Mon d n → ZMod q) :
    0 ≤ sigQ d n q a := by
  unfold sigQ
  positivity

theorem sum_primFinset_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → ℕ) [∀ i, NeZero (Q i)]
    [NeZero (∏ i, Q i)] (hQ : ∀ i j, i ≠ j → Nat.Coprime (Q i) (Q j)) (d n : ℕ) (κ : ℝ) :
    (∑ a ∈ Work.HP.NA.primFinset d n (∏ i, Q i), (Work.HP.NA.sigQ d n (∏ i, Q i) a) ^ (-κ))
      = ∏ i, (∑ a ∈ Work.HP.NA.primFinset d n (Q i), (Work.HP.NA.sigQ d n (Q i) a) ^ (-κ)) := by
  classical
  have hQ' : Pairwise (Function.onFun Nat.Coprime Q) := hQ
  -- the CRT bijection on coefficient vectors, and its inverse
  let Φ : (Work.HP.Mon d n → ZMod (∏ i, Q i)) → (∀ i, Work.HP.Mon d n → ZMod (Q i)) :=
    fun a i m => ZMod.prodEquivPi Q hQ' (a m) i
  let Φinv : (∀ i, Work.HP.Mon d n → ZMod (Q i)) → (Work.HP.Mon d n → ZMod (∏ i, Q i)) :=
    fun y m => (ZMod.prodEquivPi Q hQ').symm (fun i => y i m)
  have hleft : Function.LeftInverse Φinv Φ := by
    intro a
    show (fun m => (ZMod.prodEquivPi Q hQ').symm
      (fun i => ZMod.prodEquivPi Q hQ' (a m) i)) = a
    funext m
    exact RingEquiv.symm_apply_apply (ZMod.prodEquivPi Q hQ') (a m)
  have hright : Function.RightInverse Φinv Φ := by
    intro y
    show (fun i m => ZMod.prodEquivPi Q hQ'
      ((ZMod.prodEquivPi Q hQ').symm (fun i => y i m)) i) = y
    funext i m
    exact congrFun (RingEquiv.apply_symm_apply (ZMod.prodEquivPi Q hQ') (fun i => y i m)) i
  have hmemPrim : ∀ (q : ℕ) [NeZero q] (a : Work.HP.Mon d n → ZMod q),
      a ∈ primFinset d n q ↔ IsPrimGen q a := by
    intro q _ a
    rw [primFinset]
    simp
  -- `Φ` matches primitive vectors up with tuples of primitive vectors
  have hmem : ∀ a : Work.HP.Mon d n → ZMod (∏ i, Q i),
      a ∈ primFinset d n (∏ i, Q i) ↔
        Φ a ∈ Fintype.piFinset (fun i => primFinset d n (Q i)) := by
    intro a
    rw [Fintype.mem_piFinset]
    constructor
    · intro h i
      exact (hmemPrim (Q i) (Φ a i)).mpr
        ((isPrimGen_prodEquivPi_iff Q hQ' a).mp ((hmemPrim (∏ i, Q i) a).mp h) i)
    · intro h
      exact (hmemPrim (∏ i, Q i) a).mpr
        ((isPrimGen_prodEquivPi_iff Q hQ' a).mpr fun i => (hmemPrim (Q i) (Φ a i)).mp (h i))
  -- pointwise factorisation of `σ`
  have hsig : ∀ a : Work.HP.Mon d n → ZMod (∏ i, Q i),
      sigQ d n (∏ i, Q i) a = ∏ i, sigQ d n (Q i) (Φ a i) := fun a => sigQ_prod_crt Q hQ' d n a
  calc (∑ a ∈ primFinset d n (∏ i, Q i), (sigQ d n (∏ i, Q i) a) ^ (-κ))
      = ∑ a ∈ primFinset d n (∏ i, Q i), ∏ i, (sigQ d n (Q i) (Φ a i)) ^ (-κ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hsig a]
        exact prod_rpow_neg Finset.univ (fun i => sigQ d n (Q i) (Φ a i))
          (fun i => sigQ_nonnegative d n (Q i) (Φ a i)) κ
    _ = ∑ y ∈ Fintype.piFinset (fun i => primFinset d n (Q i)),
          ∏ i, (sigQ d n (Q i) (y i)) ^ (-κ) := by
        refine Finset.sum_bij (fun a _ => Φ a) ?_ ?_ ?_ ?_
        · intro a ha; exact (hmem a).mp ha
        · intro a₁ _ a₂ _ h
          rw [← hleft a₁, h, hleft a₂]
        · intro y hy
          exact ⟨Φinv y, (hmem (Φinv y)).mpr (by rw [hright y]; exact hy), hright y⟩
        · intro a _; rfl
    _ = ∏ i, ∑ a ∈ primFinset d n (Q i), (sigQ d n (Q i) a) ^ (-κ) :=
        (Finset.prod_univ_sum (fun i => primFinset d n (Q i))
          (fun i a => (sigQ d n (Q i) a) ^ (-κ))).symm

end Work.HP.NA
