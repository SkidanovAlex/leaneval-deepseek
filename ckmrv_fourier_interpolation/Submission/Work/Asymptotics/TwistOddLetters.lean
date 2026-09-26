/-
# The word of letters and the accumulated twisted carries

This file runs the cocycle `twist_cocycle` along a word in the *letters* `S` and `T^k`
(`k : ℤ`), i.e. along the blocks of `Work.Asymptotics.block_factorization`, accumulating the
twisted carries `(1-z)·rowDiffOdd γ 0`.

* `wblk l`, `letterA l`, `letterB l`: the group element and the two components of the twisted
  carry attached to the letter `l : Bool × ℤ` (`none` is the atom `S`, `some k` is the block
  `T^k`);
* `bAmp L = ∏_{l ∈ L} (1 + Frob (wblk l))`, the growth potential of a list of letters;
* `bAcc L i` : the accumulated twisted carry of the product of the letters of `L`;
* `bAcc_spec` : `carryCombOdd (bAcc L i) = twist (∏ letter) i` (the cocycle, by induction);
* `bAcc_bound` : polynomial bounds for `bAcc L i` in terms of `bAmp L` and `L.length`.
-/
import Mathlib
import Submission.Work.Asymptotics.TwistOddBlocks
import Submission.Work.Asymptotics.CarryBoundBasic
import Submission.Work.Asymptotics.PropagateBounds.Defs

set_option maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## The letters -/

/-- The blocks of `block_factorization`: `(false, k)` is `T^k`, `(true, k)` is `S T^k`. -/
def wblk (p : Bool × ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if p.1 then ModularGroup.S * ModularGroup.T ^ p.2 else ModularGroup.T ^ p.2

/-- The `(T-1)²`-component of the twisted carry of a block. -/
def wblkA (p : Bool × ℤ) (i : Fin 6) : R := if p.1 then STblockA p.2 i else TblockA p.2 i

/-- The `S(T-1)²`-component of the twisted carry of a block. -/
def wblkB (p : Bool × ℤ) (i : Fin 6) : R := if p.1 then STblockB p.2 i else TblockB p.2 i

/-- The growth potential of a list of letters: `2 * ∏ (1 + Frob (wblk l))`
(the factor `2` makes the empty list harmless, since `Frob 1 = √2`). -/
def bAmp (L : List (Bool × ℤ)) : ℝ := (L.map (fun l => 1 + Frob (wblk l))).prod * 2

@[simp] lemma bAmp_nil : bAmp [] = 2 := by simp [bAmp]

lemma bAmp_cons (l : Bool × ℤ) (L : List (Bool × ℤ)) :
    bAmp (l :: L) = (1 + Frob (wblk l)) * bAmp L := by
  simp only [bAmp, List.map_cons, List.prod_cons]
  ring

lemma Frob_one_le : Frob (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ≤ 2 := by
  have h2 : frobSq (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) = 2 := by decide
  rw [Frob_eq_sqrt_frobSq, h2, Nat.cast_ofNat]
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]

lemma one_le_Frob_blk (l : Bool × ℤ) : 1 ≤ Frob (wblk l) := by
  rcases l with ⟨b, k⟩
  cases b
  · exact one_le_Frob (ModularGroup.T ^ k)
  · rw [show wblk (true, k) = ModularGroup.S * ModularGroup.T ^ k from rfl, Frob_ST_zpow]
    rw [Real.one_le_sqrt]; nlinarith [sq_nonneg (k : ℝ)]

lemma one_le_one_add_Frob_blk (l : Bool × ℤ) : 1 ≤ 1 + Frob (wblk l) := by
  have := one_le_Frob_blk l; linarith

lemma one_le_bAmp (L : List (Bool × ℤ)) : 1 ≤ bAmp L := by
  induction L with
  | nil => simp
  | cons l L ih =>
    rw [bAmp_cons]
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (1 + Frob (wblk l)) * bAmp L :=
          mul_le_mul (one_le_one_add_Frob_blk l) ih (by norm_num) (by linarith [one_le_one_add_Frob_blk l])

lemma bAmp_nonneg (L : List (Bool × ℤ)) : 0 ≤ bAmp L := le_trans zero_le_one (one_le_bAmp L)

lemma bAmp_le_cons (l : Bool × ℤ) (L : List (Bool × ℤ)) : bAmp L ≤ bAmp (l :: L) := by
  rw [bAmp_cons]
  have h1 : (1 : ℝ) ≤ 1 + Frob (wblk l) := one_le_one_add_Frob_blk l
  calc bAmp L = 1 * bAmp L := (one_mul _).symm
    _ ≤ (1 + Frob (wblk l)) * bAmp L :=
        mul_le_mul_of_nonneg_right h1 (bAmp_nonneg L)

lemma one_add_Frob_blk_le_bAmp {l : Bool × ℤ} {L : List (Bool × ℤ)} (hl : l ∈ L) :
    1 + Frob (wblk l) ≤ bAmp L := by
  induction L with
  | nil => exact absurd hl List.not_mem_nil
  | cons q L ih =>
    rw [bAmp_cons]
    rcases List.mem_cons.mp hl with h | hl
    · rw [h]
      calc (1 + Frob (wblk q) : ℝ) = (1 + Frob (wblk q)) * 1 := (mul_one _).symm
        _ ≤ (1 + Frob (wblk q)) * bAmp L :=
            mul_le_mul_of_nonneg_left (one_le_bAmp L)
              (le_trans zero_le_one (one_le_one_add_Frob_blk q))
    · calc 1 + Frob (wblk l) ≤ bAmp L := ih hl
        _ = 1 * bAmp L := (one_mul _).symm
        _ ≤ (1 + Frob (wblk q)) * bAmp L :=
            mul_le_mul_of_nonneg_right (one_le_one_add_Frob_blk q) (bAmp_nonneg L)

/-- `Frob` of the product of a list of letters is at most `bAmp`. -/
lemma Frob_blk_prod_le (L : List (Bool × ℤ)) :
    Frob ((L.map wblk).prod) ≤ bAmp L := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil, bAmp_nil]
    exact Frob_one_le
  | cons l L ih =>
    rw [List.map_cons, List.prod_cons, bAmp_cons]
    have h1 : Frob (wblk l) ≤ 1 + Frob (wblk l) := by
      have := Frob_nonneg (wblk l); linarith
    have h2 : (0 : ℝ) ≤ bAmp L := bAmp_nonneg L
    calc Frob (wblk l * (L.map wblk).prod)
        ≤ Frob (wblk l) * Frob ((L.map wblk).prod) := Frob_mul_le _ _
      _ ≤ (1 + Frob (wblk l)) * bAmp L :=
          mul_le_mul h1 ih (Frob_nonneg _) (by linarith [Frob_nonneg (wblk l)])

/-! ## The accumulated carries -/

/-- The accumulated twisted carry of the product of the letters of `L`. -/
def bAcc : List (Bool × ℤ) → Fin 6 → R × R
  | [], _ => (0, 0)
  | l :: L, i =>
      (∑ j : Fin 6, (sigmaHom (wblk l)) i j • (bAcc L j).1
          + wblkA l i * ofSL ((L.map wblk).prod),
       ∑ j : Fin 6, (sigmaHom (wblk l)) i j • (bAcc L j).2
          + wblkB l i * ofSL ((L.map wblk).prod))

@[simp] lemma bAcc_nil (i : Fin 6) : bAcc [] i = (0, 0) := rfl

@[simp] lemma bAcc_cons_fst (l : Bool × ℤ) (L : List (Bool × ℤ)) (i : Fin 6) :
    (bAcc (l :: L) i).1
      = ∑ j : Fin 6, (sigmaHom (wblk l)) i j • (bAcc L j).1
          + wblkA l i * ofSL ((L.map wblk).prod) := rfl

@[simp] lemma bAcc_cons_snd (l : Bool × ℤ) (L : List (Bool × ℤ)) (i : Fin 6) :
    (bAcc (l :: L) i).2
      = ∑ j : Fin 6, (sigmaHom (wblk l)) i j • (bAcc L j).2
          + wblkB l i * ofSL ((L.map wblk).prod) := rfl

/-- `carryCombOdd` of a finite `ℂ`-linear combination. -/
lemma carryCombOdd_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (a b : ι → R) :
    carryCombOdd (∑ i ∈ s, c i • a i) (∑ i ∈ s, c i • b i)
      = ∑ i ∈ s, c i • carryCombOdd (a i) (b i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [carryCombOdd_zero]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, Finset.sum_insert hx, carryCombOdd_add,
      carryCombOdd_smul, ih]

lemma carryCombOdd_sum_univ (c : Fin 6 → ℂ) (a b : Fin 6 → R) :
    carryCombOdd (∑ j : Fin 6, c j • a j) (∑ j : Fin 6, c j • b j)
      = ∑ j : Fin 6, c j • carryCombOdd (a j) (b j) :=
  carryCombOdd_sum Finset.univ c a b

/-- The cocycle law along a word of letters. -/
theorem bAcc_spec (hblk : ∀ l i, carryCombOdd (wblkA l i) (wblkB l i) = twist (wblk l) i) :
    ∀ (L : List (Bool × ℤ)) (i : Fin 6),
      carryCombOdd (bAcc L i).1 (bAcc L i).2 = twist ((L.map wblk).prod) i := by
  intro L
  induction L with
  | nil =>
    intro i
    rw [bAcc_nil, carryCombOdd_zero, List.map_nil, List.prod_nil, twist_one]
  | cons l L ih =>
    intro i
    simp only [bAcc_cons_fst, bAcc_cons_snd]
    rw [carryCombOdd_add, carryCombOdd_sum_univ, carryCombOdd_mul_of]
    have h1 : ∀ j : Fin 6, carryCombOdd (bAcc L j).1 (bAcc L j).2
        = twist ((L.map wblk).prod) j := fun j => ih j
    simp only [h1]
    rw [hblk l i]
    exact (twist_cocycle (wblk l) ((L.map wblk).prod) i).symm


/-! ## Bounds for the accumulated carries -/

/-- **Polynomial bounds for the accumulated twisted carries.**  If the entries of `σ` on the
letters grow at most like `(1 + Frob)` to the power `Nsig` (with the extra factor `6` from the
six-term sum) and the twisted carries of the letters grow at most like `(1 + Frob l) ^ Ncar`,
then the accumulated carries of a word of letters are bounded by powers of the potential
`bAmp L = 2 ∏ (1 + Frob (wblk l))`. -/
theorem bAcc_bound (Nsig Ncar : ℕ) (hNsig : Nsig ≤ Ncar)
    (hσl : ∀ (l : Bool × ℤ) (i j : Fin 6),
      6 * ‖(sigmaHom (wblk l)) i j‖ ≤ (1 + Frob (wblk l)) ^ Nsig)
    (hcar : ∀ (l : Bool × ℤ) (i : Fin 6),
      coeffNorm (wblkA l i) ≤ (1 + Frob (wblk l)) ^ Ncar ∧
      coeffNorm (wblkB l i) ≤ (1 + Frob (wblk l)) ^ Ncar ∧
      supportFrobLe (wblkA l i) ((1 + Frob (wblk l)) ^ Ncar) ∧
      supportFrobLe (wblkB l i) ((1 + Frob (wblk l)) ^ Ncar)) :
    ∀ (L : List (Bool × ℤ)) (i : Fin 6),
      coeffNorm (bAcc L i).1 ≤ ((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar) ∧
      coeffNorm (bAcc L i).2 ≤ ((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar) ∧
      supportFrobLe (bAcc L i).1 ((bAmp L) ^ (Ncar + 1)) ∧
      supportFrobLe (bAcc L i).2 ((bAmp L) ^ (Ncar + 1)) := by
  intro L
  induction L with
  | nil =>
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [bAcc_nil, coeffNorm_zero]
    · simp [bAcc_nil, coeffNorm_zero]
    · rw [bAcc_nil]; exact supportFrobLe_zero _
    · rw [bAcc_nil]; exact supportFrobLe_zero _
  | cons l L ih =>
    intro i
    have ih1 : ∀ j : Fin 6, coeffNorm (bAcc L j).1 ≤ ((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar) :=
      fun j => (ih j).1
    have ih2 : ∀ j : Fin 6, coeffNorm (bAcc L j).2 ≤ ((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar) :=
      fun j => (ih j).2.1
    have ih3 : ∀ j : Fin 6, supportFrobLe (bAcc L j).1 ((bAmp L) ^ (Ncar + 1)) :=
      fun j => (ih j).2.2.1
    have ih4 : ∀ j : Fin 6, supportFrobLe (bAcc L j).2 ((bAmp L) ^ (Ncar + 1)) :=
      fun j => (ih j).2.2.2
    have hpow1 : (1 : ℝ) ≤ 1 + Frob (wblk l) := one_le_one_add_Frob_blk l
    have hpow0 : (0 : ℝ) ≤ 1 + Frob (wblk l) := le_trans zero_le_one hpow1
    have hAmp1 : (1 : ℝ) ≤ bAmp L := one_le_bAmp L
    have hAmp0 : (0 : ℝ) ≤ bAmp L := le_trans zero_le_one hAmp1
    have hAmpC1 : (1 : ℝ) ≤ bAmp (l :: L) := one_le_bAmp _
    have hAmpC0 : (0 : ℝ) ≤ bAmp (l :: L) := le_trans zero_le_one hAmpC1
    have hmono : bAmp L ≤ bAmp (l :: L) := bAmp_le_cons l L
    have hbase : 1 + Frob (wblk l) ≤ bAmp (l :: L) := by
      rw [bAmp_cons]
      calc (1 + Frob (wblk l) : ℝ) = (1 + Frob (wblk l)) * 1 := (mul_one _).symm
        _ ≤ (1 + Frob (wblk l)) * bAmp L := mul_le_mul_of_nonneg_left hAmp1 hpow0
    have hpowAmp : (1 + Frob (wblk l)) ^ Ncar * (bAmp L) ^ Ncar = (bAmp (l :: L)) ^ Ncar := by
      rw [bAmp_cons, mul_pow]
    have hAmpL2 : (0 : ℝ) ≤ (bAmp L) ^ (2 * Ncar) := pow_nonneg hAmp0 _
    have hAmpL2one : (1 : ℝ) ≤ (bAmp L) ^ (2 * Ncar) := one_le_pow₀ hAmp1
    have hAmpC2 : (0 : ℝ) ≤ (bAmp (l :: L)) ^ (2 * Ncar) := pow_nonneg hAmpC0 _
    have hrow : (∑ j : Fin 6, ‖(sigmaHom (wblk l)) i j‖)
        ≤ (1 + Frob (wblk l)) ^ Nsig := by
      have h6 : (0 : ℝ) < 6 := by norm_num
      have h1 : ∀ j : Fin 6, ‖(sigmaHom (wblk l)) i j‖
          ≤ (1 + Frob (wblk l)) ^ Nsig / 6 := by
        intro j
        rw [le_div_iff₀ h6]
        linarith [hσl l i j]
      calc (∑ j : Fin 6, ‖(sigmaHom (wblk l)) i j‖)
          ≤ ∑ _j : Fin 6, (1 + Frob (wblk l)) ^ Nsig / 6 := Finset.sum_le_sum fun j _ => h1 j
        _ = (1 + Frob (wblk l)) ^ Nsig := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring_nf
    have hrow' : (∑ j : Fin 6, ‖(sigmaHom (wblk l)) i j‖)
        ≤ (1 + Frob (wblk l)) ^ Ncar :=
      le_trans hrow (pow_le_pow_right₀ hpow1 hNsig)
    -- the head sum is bounded by the same potential as the tail
    have hsumGen : ∀ (X : Fin 6 → R),
        (∀ j, coeffNorm (X j) ≤ ((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar)) →
        coeffNorm (∑ j : Fin 6, (sigmaHom (wblk l)) i j • X j)
          ≤ ((L.length : ℝ) + 1) * (bAmp (l :: L)) ^ (2 * Ncar) := by
      intro X hX
      refine le_trans (coeffNorm_smul_sum_le Finset.univ _ _) ?_
      refine le_trans (Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hX j) (norm_nonneg _)) ?_
      rw [← Finset.sum_mul]
      calc (∑ j : Fin 6, ‖(sigmaHom (wblk l)) i j‖)
            * (((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar))
          ≤ (1 + Frob (wblk l)) ^ Ncar * (((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar)) :=
            mul_le_mul_of_nonneg_right hrow' (by positivity)
        _ ≤ (1 + Frob (wblk l)) ^ (2 * Ncar)
              * (((L.length : ℝ) + 1) * (bAmp L) ^ (2 * Ncar)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact pow_le_pow_right₀ hpow1 (by omega)
        _ = ((L.length : ℝ) + 1) * (bAmp (l :: L)) ^ (2 * Ncar) := by
            rw [bAmp_cons, mul_pow]; ring_nf
    -- the two letter terms are bounded by the same potential
    have hletBase : (1 + Frob (wblk l)) ^ Ncar ≤ (bAmp (l :: L)) ^ (2 * Ncar) := by
      calc (1 + Frob (wblk l)) ^ Ncar ≤ (1 + Frob (wblk l)) ^ (2 * Ncar) :=
            pow_le_pow_right₀ hpow1 (by omega)
        _ ≤ (bAmp (l :: L)) ^ (2 * Ncar) := pow_le_pow_left₀ hpow0 hbase (2 * Ncar)
    have hlet1 : coeffNorm (wblkA l i * ofSL ((L.map wblk).prod))
        ≤ (bAmp (l :: L)) ^ (2 * Ncar) :=
      le_trans (le_trans (coeffNorm_mul_of_le _ _) (hcar l i).1) hletBase
    have hlet2 : coeffNorm (wblkB l i * ofSL ((L.map wblk).prod))
        ≤ (bAmp (l :: L)) ^ (2 * Ncar) :=
      le_trans (le_trans (coeffNorm_mul_of_le _ _) (hcar l i).2.1) hletBase
    -- combine
    have hcomb : ∀ x y : ℝ, x ≤ ((L.length : ℝ) + 1) * (bAmp (l :: L)) ^ (2 * Ncar) →
        y ≤ (bAmp (l :: L)) ^ (2 * Ncar) →
        x + y ≤ (((l :: L).length : ℝ) + 1) * (bAmp (l :: L)) ^ (2 * Ncar) := by
      intro x y hx hy
      have hlen : (((l :: L).length : ℝ) + 1) = ((L.length : ℝ) + 1) + 1 := by
        rw [List.length_cons]; push_cast; ring
      rw [hlen]
      linarith
    -- support bounds
    have hpowAmp' : (1 + Frob (wblk l)) ^ Ncar * bAmp L ≤ (bAmp (l :: L)) ^ (Ncar + 1) := by
      calc (1 + Frob (wblk l)) ^ Ncar * bAmp L
          = (1 + Frob (wblk l)) ^ Ncar * bAmp L * 1 := by ring
        _ ≤ (1 + Frob (wblk l)) ^ Ncar * bAmp L
              * ((1 + Frob (wblk l)) * (bAmp L) ^ Ncar) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
              _ ≤ (1 + Frob (wblk l)) * (bAmp L) ^ Ncar :=
                  mul_le_mul hpow1 (one_le_pow₀ hAmp1) (by norm_num) hpow0
        _ = ((1 + Frob (wblk l)) * bAmp L) ^ (Ncar + 1) := by
            rw [pow_succ, mul_pow]; ring
        _ = (bAmp (l :: L)) ^ (Ncar + 1) := by rw [bAmp_cons]
    have hsuppSum1 : supportFrobLe (∑ j : Fin 6, (sigmaHom (wblk l)) i j • (bAcc L j).1)
        ((bAmp (l :: L)) ^ (Ncar + 1)) :=
      supportFrobLe_mono (supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => ih3 j))
        (pow_le_pow_left₀ hAmp0 hmono (Ncar + 1))
    have hsuppSum2 : supportFrobLe (∑ j : Fin 6, (sigmaHom (wblk l)) i j • (bAcc L j).2)
        ((bAmp (l :: L)) ^ (Ncar + 1)) :=
      supportFrobLe_mono (supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => ih4 j))
        (pow_le_pow_left₀ hAmp0 hmono (Ncar + 1))
    have hsuppProd1 : supportFrobLe (wblkA l i * ofSL ((L.map wblk).prod))
        ((bAmp (l :: L)) ^ (Ncar + 1)) :=
      supportFrobLe_mono (supportFrobLe_mul_of (hcar l i).2.2.1 _) (by
        calc (1 + Frob (wblk l)) ^ Ncar * Frob ((L.map wblk).prod)
            ≤ (1 + Frob (wblk l)) ^ Ncar * bAmp L :=
              mul_le_mul_of_nonneg_left (Frob_blk_prod_le L) (by positivity)
          _ ≤ (bAmp (l :: L)) ^ (Ncar + 1) := hpowAmp')
    have hsuppProd2 : supportFrobLe (wblkB l i * ofSL ((L.map wblk).prod))
        ((bAmp (l :: L)) ^ (Ncar + 1)) :=
      supportFrobLe_mono (supportFrobLe_mul_of (hcar l i).2.2.2 _) (by
        calc (1 + Frob (wblk l)) ^ Ncar * Frob ((L.map wblk).prod)
            ≤ (1 + Frob (wblk l)) ^ Ncar * bAmp L :=
              mul_le_mul_of_nonneg_left (Frob_blk_prod_le L) (by positivity)
          _ ≤ (bAmp (l :: L)) ^ (Ncar + 1) := hpowAmp')
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [bAcc_cons_fst]
      exact le_trans (coeffNorm_add_le _ _) (hcomb _ _ (hsumGen _ ih1) hlet1)
    · rw [bAcc_cons_snd]
      exact le_trans (coeffNorm_add_le _ _) (hcomb _ _ (hsumGen _ ih2) hlet2)
    · rw [bAcc_cons_fst]
      refine supportFrobLe_mono (supportFrobLe_add hsuppSum1 hsuppProd1) ?_
      exact le_of_eq (max_self _)
    · rw [bAcc_cons_snd]
      refine supportFrobLe_mono (supportFrobLe_add hsuppSum2 hsuppProd2) ?_
      exact le_of_eq (max_self _)

end Work.Asymptotics
