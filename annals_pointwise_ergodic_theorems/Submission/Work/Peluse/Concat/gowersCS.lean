/-
Pointwise ergodic theorems for non-conventional bilinear polynomial averages (Krause--Mirek--Tao),
the "Gowers--Cauchy--Schwarz" inequality of Peluse's Lemma 2.2 in the flat-cube form used by the
concatenation chapter: the correlation of `f` with a product of `1`-bounded functions, each
independent of one coordinate, is bounded by the Gowers box norm of `f` raised to `2 ^ s`.

The proof is Peluse's: the Gowers--Cauchy--Schwarz inequality for the flat cube
(`gcs_core` below, an induction on the dimension with one Cauchy--Schwarz and one Hoelder step,
following Green--Tao, *Linear equations in primes*, Lemma B.2), applied to the family
`substF f g` of Lemma 2.2, whose cube sum is computed explicitly.
-/
import Mathlib
import Submission.Work.Peluse.Concat.gcsRecurse
import Submission.Work.Peluse.Concat.gcsSplit
import Submission.Work.Peluse.Concat.gcsSubst
import Submission.Work.Peluse.Concat.gcsSubstProd
import Submission.Work.Peluse.BoxNorm.genHolder
import Submission.Work.Peluse.BoxNorm.cauchySchwarzC

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

lemma sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x^2) ^ (1/(2:ℝ)) = x := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

lemma sq_rpow_half_one {x : ℝ} (hx : 0 ≤ x) : (x^2) ^ (1/(2:ℝ)^1) = x := by
  rw [show (1:ℝ)/(2:ℝ)^1 = 1/(2:ℝ) from by norm_num]
  exact sq_rpow_half hx

lemma rpow_half_sq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ (1/(2:ℝ)^n) = (x ^ (1/(2:ℝ)^(n+1)))^2 := by
  have hexp : (1/(2:ℝ)^(n+1)) * ((2:ℕ) : ℝ) = 1/(2:ℝ)^n := by
    rw [pow_succ]
    field_simp
    ring
  rw [← Real.rpow_natCast (x ^ (1/(2:ℝ)^(n+1))) 2, ← Real.rpow_mul hx, hexp]

lemma rpow_mul_self {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x ^ (1/(2:ℝ)^n)) ^ (2^n) = x := by
  have hexp : (1/(2:ℝ)^n) * ((2^n : ℕ) : ℝ) = 1 := by
    push_cast
    rw [one_div, inv_mul_cancel₀ (by positivity : ((2:ℝ)^n) ≠ 0)]
  rw [← Real.rpow_natCast (x ^ (1/(2:ℝ)^n)) (2^n), ← Real.rpow_mul hx, hexp, Real.rpow_one]

lemma prod_rpow_half_sq {n : ℕ} (c : (Fin n → Bool) → ℝ) (hc : ∀ ω, 0 ≤ c ω) :
    (∏ ω' : Fin n → Bool, c ω' ^ (1/(2:ℝ)^n))
      = (∏ ω' : Fin n → Bool, c ω' ^ (1/(2:ℝ)^(n+1)))^2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun ω' _ => rpow_half_sq (hc ω') n)

lemma R0R1_eq {n : ℕ} (c : (Fin (n+1) → Bool) → ℝ) (hc : ∀ ω, 0 ≤ c ω) :
    (∏ ω' : Fin n → Bool, c (Fin.cons false ω') ^ (1/(2:ℝ)^n))
      * (∏ ω' : Fin n → Bool, c (Fin.cons true ω') ^ (1/(2:ℝ)^n))
    = (∏ ω : Fin (n+1) → Bool, c ω ^ (1/(2:ℝ)^(n+1)))^2 := by
  have hsplit : (∏ ω' : Fin n → Bool, c (Fin.cons false ω') ^ (1/(2:ℝ)^(n+1)))
        * (∏ ω' : Fin n → Bool, c (Fin.cons true ω') ^ (1/(2:ℝ)^(n+1)))
      = ∏ ω : Fin (n+1) → Bool, c ω ^ (1/(2:ℝ)^(n+1)) :=
    (prod_fin_succ_bool n (fun ω => c ω ^ (1/(2:ℝ)^(n+1)))).symm
  rw [prod_rpow_half_sq (c := fun ω' => c (Fin.cons false ω')) (hc := fun ω' => hc _),
      prod_rpow_half_sq (c := fun ω' => c (Fin.cons true ω')) (hc := fun ω' => hc _),
      ← mul_pow, hsplit]

theorem gcs_core
    (hCubeOne : ∀ {X : Type} [Fintype X] (g : (Fin 1 → X) → ℂ),
        NPow 1 g = ‖∑ x : X, g (fun _ : Fin 1 => x)‖ ^ 2)
    (hSplit : ∀ {X : Type} [Fintype X] (t : ℕ)
        (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ),
        cubeSum F = ∑ p : (Fin t → X) × (Fin t → X),
          (∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons false ω') (Fin.cons u (mix ω' p.1 p.2))))
            * star (∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons true ω') (Fin.cons u (mix ω' p.1 p.2)))))
    (hZb : ∀ {X : Type} [Fintype X] (t : ℕ)
        (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ) (b : Bool),
        (∑ p : (Fin t → X) × (Fin t → X),
            ‖∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
                (F (Fin.cons b ω') (Fin.cons u (mix ω' p.1 p.2)))‖ ^ 2)
          ≤ ∑ u0 : X, ∑ u1 : X,
              ‖cubeSum (fun (ω' : Fin t → Bool) => fun (y : Fin t → X) =>
                  F (Fin.cons b ω') (Fin.cons u0 y) * star (F (Fin.cons b ω') (Fin.cons u1 y)))‖)
    (hRec : ∀ {X : Type} [Fintype X] (t : ℕ), 1 ≤ t → ∀ (g : (Fin (t+1) → X) → ℂ),
        NPow (t+1) g = ∑ u0 : X, ∑ u1 : X,
          NPow t (fun y : Fin t → X => g (Fin.cons u0 y) * star (g (Fin.cons u1 y))))
    : ∀ {X : Type} [Fintype X] (t : ℕ), 1 ≤ t → ∀ (F : (Fin t → Bool) → (Fin t → X) → ℂ),
        ‖cubeSum F‖ ≤ ∏ ω : Fin t → Bool, (NPow t (F ω)) ^ (1/(2:ℝ)^t) := by
  intro X _inst
  have H : ∀ (t : ℕ), 1 ≤ t → ∀ (F : (Fin t → Bool) → (Fin t → X) → ℂ),
      ‖cubeSum F‖ ≤ ∏ ω : Fin t → Bool, (NPow t (F ω)) ^ (1/(2:ℝ)^t) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      intro F
      have hprod : ∀ x0 x1 : Fin 1 → X,
          cubeProd F x0 x1
            = F (fun _ : Fin 1 => false) x0 * star (F (fun _ : Fin 1 => true) x1) := by
        intro x0 x1
        rw [cubeProd, prod_fin_one_bool (M := ℂ)]
        simp only [weight_fin_one_true, weight_fin_one_false, mix_fin_one_true,
          mix_fin_one_false, Function.iterate_one, Function.iterate_zero_apply]
        exact mul_comm _ _
      rw [cubeSum]
      simp only [hprod]
      have hstep1 : ∀ x0 : Fin 1 → X,
          (∑ x1 : Fin 1 → X,
              F (fun _ : Fin 1 => false) x0 * star (F (fun _ : Fin 1 => true) x1))
            = F (fun _ : Fin 1 => false) x0
              * star (∑ x1 : Fin 1 → X, F (fun _ : Fin 1 => true) x1) := by
        intro x0
        rw [← Finset.mul_sum, ← star_sum]
      simp only [hstep1]
      rw [← Finset.sum_mul]
      rw [sum_fin1 (fun v => F (fun _ : Fin 1 => false) v),
          sum_fin1 (fun v => F (fun _ : Fin 1 => true) v)]
      rw [norm_mul, norm_star]
      rw [prod_fin_one_bool (M := ℝ)]
      rw [hCubeOne (F (fun _ : Fin 1 => true)), hCubeOne (F (fun _ : Fin 1 => false))]
      have e1 : (‖∑ x : X, F (fun _ : Fin 1 => true) (fun _ : Fin 1 => x)‖^2) ^ (1/(2:ℝ)^1)
          = ‖∑ x : X, F (fun _ : Fin 1 => true) (fun _ : Fin 1 => x)‖ :=
        sq_rpow_half_one (norm_nonneg _)
      have e2 : (‖∑ x : X, F (fun _ : Fin 1 => false) (fun _ : Fin 1 => x)‖^2) ^ (1/(2:ℝ)^1)
          = ‖∑ x : X, F (fun _ : Fin 1 => false) (fun _ : Fin 1 => x)‖ :=
        sq_rpow_half_one (norm_nonneg _)
      rw [e1, e2, mul_comm]
    | succ n hn ih =>
      intro F
      have ih' : ∀ (G : (Fin n → Bool) → (Fin n → X) → ℂ),
          ‖cubeSum G‖ ≤ ∏ ω' : Fin n → Bool, (NPow n (G ω')) ^ (1/(2:ℝ)^n) := ih
      have hZbnd : ∀ b : Bool,
          (∑ p : (Fin n → X) × (Fin n → X),
              ‖∑ u : X, ∏ ω' : Fin n → Bool, (star^[Work.Peluse.weight ω'])
                  (F (Fin.cons b ω') (Fin.cons u (mix ω' p.1 p.2)))‖ ^ 2)
            ≤ ∏ ω' : Fin n → Bool, (NPow (n+1) (F (Fin.cons b ω'))) ^ (1/(2:ℝ)^n) := by
        intro b
        refine le_trans (hZb n F b) ?_
        have hsum : (∑ u0 : X, ∑ u1 : X,
              ‖cubeSum (fun (ω' : Fin n → Bool) => fun (y : Fin n → X) =>
                  F (Fin.cons b ω') (Fin.cons u0 y)
                    * star (F (Fin.cons b ω') (Fin.cons u1 y)))‖)
            = ∑ p : X × X,
              ‖cubeSum (fun (ω' : Fin n → Bool) => fun (y : Fin n → X) =>
                  F (Fin.cons b ω') (Fin.cons p.1 y)
                    * star (F (Fin.cons b ω') (Fin.cons p.2 y)))‖ := by
          rw [Fintype.sum_prod_type]
        rw [hsum]
        refine le_trans (Finset.sum_le_sum (fun p _ => ih' _)) ?_
        have hgen := Work.Peluse.BoxNorm.genHolder (X := X × X)
          (a := fun ω' (p : X × X) =>
            (NPow n (fun y : Fin n → X => F (Fin.cons b ω') (Fin.cons p.1 y)
              * star (F (Fin.cons b ω') (Fin.cons p.2 y)))) ^ (1/(2:ℝ)^n))
          (fun ω' p => Real.rpow_nonneg (NPow_nonneg n _) _)
        refine le_trans hgen (le_of_eq ?_)
        refine Finset.prod_congr rfl (fun ω' _ => ?_)
        have hbase : (∑ p : X × X,
              ((NPow n (fun y : Fin n → X => F (Fin.cons b ω') (Fin.cons p.1 y)
                * star (F (Fin.cons b ω') (Fin.cons p.2 y)))) ^ (1/(2:ℝ)^n)) ^ (2^n))
            = NPow (n+1) (F (Fin.cons b ω')) := by
          rw [Finset.sum_congr rfl (fun p _ => rpow_mul_self (NPow_nonneg n _) n),
              Fintype.sum_prod_type]
          exact (hRec n hn (F (Fin.cons b ω'))).symm
        rw [hbase]
      have hCs : ‖cubeSum F‖ ^ 2 ≤
          (∑ p : (Fin n → X) × (Fin n → X),
              ‖∑ u : X, ∏ ω' : Fin n → Bool, (star^[Work.Peluse.weight ω'])
                  (F (Fin.cons false ω') (Fin.cons u (mix ω' p.1 p.2)))‖ ^ 2)
            * (∑ p : (Fin n → X) × (Fin n → X),
              ‖∑ u : X, ∏ ω' : Fin n → Bool, (star^[Work.Peluse.weight ω'])
                  (F (Fin.cons true ω') (Fin.cons u (mix ω' p.1 p.2)))‖ ^ 2) := by
        rw [hSplit n F]
        exact Work.Peluse.BoxNorm.cauchySchwarzC Finset.univ
          (fun p : (Fin n → X) × (Fin n → X) =>
            ∑ u : X, ∏ ω' : Fin n → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons false ω') (Fin.cons u (mix ω' p.1 p.2))))
          (fun p : (Fin n → X) × (Fin n → X) =>
            ∑ u : X, ∏ ω' : Fin n → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons true ω') (Fin.cons u (mix ω' p.1 p.2))))
      have hsq : ‖cubeSum F‖ ^ 2 ≤
          (∏ ω : Fin (n+1) → Bool, (NPow (n+1) (F ω)) ^ (1/(2:ℝ)^(n+1)))^2 := by
        refine le_trans hCs ?_
        rw [← R0R1_eq (c := fun ω => NPow (n+1) (F ω)) (hc := fun ω => NPow_nonneg _ _)]
        exact mul_le_mul (hZbnd false) (hZbnd true) (by positivity)
          (Finset.prod_nonneg (fun ω _ => Real.rpow_nonneg (NPow_nonneg _ _) _))
      have hfin := sq_le_sq.mp hsq
      rw [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (Finset.prod_nonneg (fun ω _ => Real.rpow_nonneg (NPow_nonneg _ _) _))] at hfin
      exact hfin
  intro t ht F
  exact H t ht F



/-- `‖(a : ℂ)‖ = a` for `a ≥ 0`. -/
lemma norm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖(a : ℂ)‖ = a := by
  refine (sq_eq_sq₀ (norm_nonneg _) ha).mp ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

lemma nat_one_le_two_pow (s : ℕ) : (1:ℕ) ≤ 2^s := Nat.one_le_two_pow

/-- The Gowers--Cauchy--Schwarz bound for the substitution family, from `gcs_core`. -/
lemma asm_hgc {X : Type} [Fintype X] {s : ℕ} (hs : 1 ≤ s)
    (F : (Fin s → Bool) → (Fin s → X) → ℂ) :
    ‖cubeSum F‖ ≤ ∏ ω : Fin s → Bool, (NPow s (F ω)) ^ (1/(2:ℝ)^s) :=
  gcs_core
    (fun {Y : Type} [Fintype Y] (g : (Fin 1 → Y) → ℂ) => by
      rw [NPow, gcsRecurse.1 Y g]
      exact norm_ofReal_of_nonneg (sq_nonneg _))
    (fun {Y : Type} [Fintype Y] (t : ℕ)
        (F : (Fin (t+1) → Bool) → (Fin (t+1) → Y) → ℂ) => gcsSplit.1 Y t F)
    (fun {Y : Type} [Fintype Y] (t : ℕ)
        (F : (Fin (t+1) → Bool) → (Fin (t+1) → Y) → ℂ) (b : Bool) => gcsSplit.2 Y t F b)
    (fun {Y : Type} [Fintype Y] (t : ℕ) (ht : 1 ≤ t)
        (g : (Fin (t+1) → Y) → ℂ) => gcsRecurse.2.2 Y t ht g)
    s hs F

/-- The product bound for the substitution family. -/
lemma asm_hprod {X : Type} [Fintype X] {s : ℕ} (hs : 1 ≤ s)
    (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (hg1 : ∀ (i : Fin s) (x : Fin s → X), ‖g i x‖ ≤ 1)
    (hg2 : ∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') :
    (∏ ω : Fin s → Bool, NPow s (substF f g ω))
      ≤ NPow s f * (((Fintype.card X : ℝ)) ^ (2*s)) ^ (2^s - 1) :=
  gcsSubstProd (X := X) (s := s) hs f g hg1 hg2

/-- The cube sum of the substitution family. -/
lemma asm_hcs {X : Type} [Fintype X] {s : ℕ} (hs : 1 ≤ s)
    (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (hg2 : ∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') :
    cubeSum (substF f g)
      = ((Fintype.card X : ℂ)) ^ s * ∑ x : Fin s → X, f x * ∏ i : Fin s, g i x :=
  gcsSubst.2.1 (X := X) (s := s) hs f g hg2

/-- The key estimate: `‖cubeSum (substF f g)‖ ^ (2^s) ≤ NPow s f * (card X ^ (2s)) ^ (2^s - 1)`. -/
lemma asm_key {X : Type} [Fintype X] {s : ℕ} (hs : 1 ≤ s)
    (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (hg1 : ∀ (i : Fin s) (x : Fin s → X), ‖g i x‖ ≤ 1)
    (hg2 : ∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') :
    ‖cubeSum (substF f g)‖ ^ (2^s)
      ≤ NPow s f * (((Fintype.card X : ℝ)) ^ (2*s)) ^ (2^s - 1) := by
  have hgc := asm_hgc (X := X) (s := s) hs (substF f g)
  have hprod := asm_hprod (X := X) (s := s) hs f g hg1 hg2
  calc ‖cubeSum (substF f g)‖ ^ (2^s)
      ≤ (∏ ω : Fin s → Bool, (NPow s (substF f g ω)) ^ (1/(2:ℝ)^s)) ^ (2^s) :=
        pow_le_pow_left₀ (norm_nonneg _) hgc (2^s)
    _ = ∏ ω : Fin s → Bool, NPow s (substF f g ω) := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl (fun ω _ =>
          rpow_mul_self (NPow_nonneg s (substF f g ω)) s)
    _ ≤ NPow s f * (((Fintype.card X : ℝ)) ^ (2*s)) ^ (2^s - 1) := hprod

/-- The rewriting of the target's left-hand side. -/
lemma asm_L {X : Type} [Fintype X] {s : ℕ} (hs : 1 ≤ s) (hcard : Fintype.card X ≠ 0)
    (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ)
    (hg2 : ∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') :
    ((Fintype.card X : ℂ))⁻¹ ^ s * (∑ x : Fin s → X, f x * ∏ i : Fin s, g i x)
      = ((Fintype.card X : ℂ))⁻¹ ^ (2*s) * cubeSum (substF f g) := by
  have hcs := asm_hcs (X := X) (s := s) hs f g hg2
  have h1 : ((Fintype.card X : ℂ))⁻¹ ^ (2*s) * ((Fintype.card X : ℂ))^s
      = ((Fintype.card X : ℂ))⁻¹ ^ s := by
    rw [show 2*s = s + s by ring, pow_add, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ (by rw [Nat.cast_ne_zero]; exact hcard), one_pow, mul_one]
  rw [hcs, ← mul_assoc, h1]

/-- The elementary real arithmetic of the final step. -/
lemma final_arith {n A P : ℝ} {s : ℕ} (hn : 0 < n)
    (hkey : A ^ (2^s) ≤ P * ((n^(2*s))^(2^s-1))) :
    (n⁻¹ ^ (2*s) * A) ^ (2^s) ≤ n⁻¹ ^ (2*s) * P := by
  have ha0 : n⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hn)
  set a : ℝ := n⁻¹ with ha'
  have hconv : (n^(2*s))^(2^s-1) = (a^(2*s*(2^s-1)))⁻¹ := by
    rw [← pow_mul, ha', inv_pow, inv_inv]
  have hM : 2*s*2^s = 2*s*(2^s-1) + 2*s := by
    conv_lhs => rw [← Nat.sub_add_cancel (nat_one_le_two_pow s)]
    rw [mul_add, mul_one]
  have hcancel : a^(2*s*2^s) * ((n^(2*s))^(2^s-1)) = a^(2*s) := by
    rw [hconv, hM, pow_add, mul_comm (a^(2*s*(2^s-1))) _,
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha0), mul_one]
  have hstep : (n⁻¹ ^ (2*s))^(2^s) * P * ((n^(2*s))^(2^s-1)) = n⁻¹^(2*s) * P := by
    have h4 : (n⁻¹ ^ (2*s))^(2^s) * ((n^(2*s))^(2^s-1)) = n⁻¹^(2*s) := by
      rw [← pow_mul]
      exact hcancel
    calc (n⁻¹ ^ (2*s))^(2^s) * P * ((n^(2*s))^(2^s-1))
        = ((n⁻¹ ^ (2*s))^(2^s) * ((n^(2*s))^(2^s-1))) * P := by ring
      _ = n⁻¹^(2*s) * P := by rw [h4]
  calc (n⁻¹ ^ (2*s) * A) ^ (2^s)
      = (n⁻¹ ^ (2*s))^(2^s) * A^(2^s) := by rw [mul_pow]
    _ ≤ (n⁻¹ ^ (2*s))^(2^s) * (P * ((n^(2*s))^(2^s-1))) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (n⁻¹ ^ (2*s))^(2^s) * P * ((n^(2*s))^(2^s-1)) := by ring
    _ = n⁻¹^(2*s) * P := hstep


theorem gowersCS : ∀ (s : ℕ) (X : Type) [Fintype X] (f : (Fin s → X) → ℂ) (g : Fin s → (Fin s → X) → ℂ),
    (∀ (i : Fin s) (x : Fin s → X), ‖g i x‖ ≤ 1) →
    (∀ (i : Fin s) (x x' : Fin s → X), (∀ j, j ≠ i → x j = x' j) → g i x = g i x') →
    ‖(Fintype.card X : ℂ)⁻¹ ^ s * ∑ x : Fin s → X, f x * ∏ i : Fin s, g i x‖ ^ (2 ^ s)
      ≤ ‖(Fintype.card X : ℂ)⁻¹ ^ (2 * s) * ∑ x0 : Fin s → X, ∑ x1 : Fin s → X,
          ∏ ω : Fin s → Bool,
            (star^[Work.Peluse.weight ω]) (f (fun i => if ω i then x1 i else x0 i))‖ := by
  intro s X _inst f g hg1 hg2
  show ‖(Fintype.card X : ℂ)⁻¹ ^ s * ∑ x : Fin s → X, f x * ∏ i : Fin s, g i x‖ ^ (2 ^ s)
      ≤ ‖(Fintype.card X : ℂ)⁻¹ ^ (2 * s) * cubeSum (fun (_ : Fin s → Bool) => f)‖
  rcases Nat.eq_zero_or_pos s with h0 | hs
  · subst h0
    haveI : Unique (Fin 0 → X) := ⟨⟨fun i => i.elim0⟩, fun a => funext fun i => i.elim0⟩
    haveI : Unique (Fin 0 → Bool) := ⟨⟨fun i => i.elim0⟩, fun a => funext fun i => i.elim0⟩
    simp [Work.Peluse.weight, mix, cubeSum, cubeProd]
    refine le_of_eq (congrArg (fun z : Fin 0 → X => ‖f z‖) ?_)
    exact Subsingleton.elim _ _
  · have hs1 : 1 ≤ s := hs
    by_cases hcard : Fintype.card X = 0
    · haveI : IsEmpty (Fin s → X) :=
        ⟨fun h => (Fintype.card_eq_zero_iff.mp hcard).false (h ⟨0, hs1⟩)⟩
      have h1 : (∑ x : Fin s → X, f x * ∏ i : Fin s, g i x) = 0 := by
        simp [Finset.univ_eq_empty]
      have h2 : cubeSum (fun (_ : Fin s → Bool) => f) = 0 := by
        simp [cubeSum, Finset.univ_eq_empty]
      rw [h1, h2]
      simp [hcard, show s ≠ 0 by omega]
    · have hkey := asm_key (X := X) (s := s) hs1 f g hg1 hg2
      have hL := asm_L (X := X) (s := s) hs1 (by omega : Fintype.card X ≠ 0) f g hg2
      have hnrpos : (0:ℝ) < (Fintype.card X : ℝ) := by
        have hpos : (0:ℕ) < Fintype.card X := Nat.pos_of_ne_zero (by omega)
        exact_mod_cast hpos
      have hnormN : ‖((Fintype.card X : ℂ))‖ = ((Fintype.card X : ℝ)) := by
        refine (sq_eq_sq₀ (norm_nonneg _) (le_of_lt hnrpos)).mp ?_
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_natCast]
        ring
      rw [hL, norm_mul, norm_pow, norm_inv, hnormN,
          norm_mul, norm_pow, norm_inv, hnormN]
      exact final_arith (n := (Fintype.card X : ℝ))
        (A := ‖cubeSum (substF f g)‖)
        (P := ‖cubeSum (fun (_ : Fin s → Bool) => f)‖) hnrpos hkey

end

end Work.Peluse.Concat
