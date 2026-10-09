import Mathlib
import Submission.Work.SSGRoute.zz3.ThetaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Λ`-invariance of `thetaFun`

The map `thetaFun n : TT n → Q_{(4,1)}` is additive (`thetaFun_add`, in `ThetaProps`) and, on the
basis of the indicator functions, satisfies

* `thetaFun n (Pi.single v 1) = lw n v`    (`thetaFun_single`);
* `thetaFun n (LamT n (Pi.single w 1)) = lw n w`   (`thetaFun_Lam_single`),

the second being the Jacobi identity `⁅⁅x,y⁆,z⁆·⁅⁅y,z⁆,x⁆·⁅⁅z,x⁆,y⁆ = 1` in `Q_{(4,1)}`
(`mkQ_jacobi`) together with the skew-symmetry `[[y,x],z] = [[x,y],z]` (`mkQ_commutator_swap`).

Since `Λ` is additive and homogeneous (`LamT_add`, `LamT_smul`) this gives the global identity

  `thetaFun n (LamT n g) = thetaFun n g`   (`thetaFun_LamT`),

proved by an induction over the list `idxList n` that splits off one indicator function at a time.
-/

open scoped commutatorElement

noncomputable section

namespace Work.SSGRoute.zz3

open Work.CohomologicalShrinking
open Work.SSGRoute.ZZ3

/-! ## Elementary list/indicator lemmas -/

/-- Evaluating a list sum of functions pointwise. -/
theorem list_sum_apply {ι M : Type*} [AddCommMonoid M] (L : List (ι → M)) (v : ι) :
    L.sum v = (L.map (fun g => g v)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.sum_cons, ih]

/-- `thetaFun` of `0` is `1`. -/
theorem thetaFun_zero' (n : ℕ) : thetaFun n (0 : TT n) = 1 := by
  rw [thetaFun_eq]
  exact List.prod_eq_one (fun y hy => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hy
    rw [Pi.zero_apply, ZMod.val_zero, pow_zero])

/-- `thetaFun` turns a list sum into a product. -/
theorem thetaFun_listSum (n : ℕ) (L : List (TT n)) :
    thetaFun n L.sum = (L.map (fun h => thetaFun n h)).prod := by
  induction L with
  | nil => simpa using thetaFun_zero' n
  | cons a L ih => rw [List.sum_cons, List.map_cons, List.prod_cons, thetaFun_add, ih]

/-- `thetaFun` is homogeneous for the `𝔽₂`-scalar action. -/
theorem thetaFun_smul (n : ℕ) (k : ZMod 2) (h : TT n) :
    thetaFun n (k • h) = (thetaFun n h) ^ (k.val) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  rw [Nat.cast_smul_eq_nsmul]
  rcases Nat.eq_zero_or_pos k.val with h0 | hpos
  · rw [h0, zero_nsmul, pow_zero]
    exact thetaFun_zero' n
  · have h1 : k.val = 1 := by
      have := ZMod.val_lt (n := 2) k
      omega
    rw [h1, one_nsmul, pow_one]

/-! ## Linearity of `Λ` -/

theorem LamT_zero (n : ℕ) : LamT n (0 : TT n) = 0 := by
  funext w
  simp [LamT_apply]

theorem LamT_add (n : ℕ) (g h : TT n) : LamT n (g + h) = LamT n g + LamT n h := by
  funext w
  simp only [LamT_apply, Pi.add_apply]
  ring

theorem LamT_smul (n : ℕ) (k : ZMod 2) (g : TT n) : LamT n (k • g) = k • LamT n g := by
  funext w
  simp only [LamT_apply, Pi.smul_apply]
  ring

/-! ## The value of `thetaFun` on indicator functions -/

/-- The product of the `lw`-classes over the `idxList`, with only one nonzero exponent, is the
single `lw`-class. -/
theorem prod_delta (n : ℕ) (v : Idx n) (L : List (Idx n)) (hnd : L.Nodup) (hmem : v ∈ L) :
    (L.map (fun w => (mkQ n (lcF n w)) ^ ((Pi.single v 1 : TT n) w).val)).prod = lw n v := by
  induction L with
  | nil => simp at hmem
  | cons a L ih =>
      rw [List.map_cons, List.prod_cons]
      by_cases hav : a = v
      · have hL : (L.map (fun w => (mkQ n (lcF n w)) ^ ((Pi.single v 1 : TT n) w).val)).prod
            = 1 := by
          apply List.prod_eq_one
          intro y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
          have hwa : w ≠ a := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hw)
          have hwv : w ≠ v := fun h => hwa (hav ▸ h)
          rw [Pi.single_eq_of_ne hwv, ZMod.val_zero, pow_zero]
        rw [hL, mul_one]
        rw [show (Pi.single v (1 : ZMod 2) : TT n) a = 1 from by rw [← hav, Pi.single_eq_same],
          show ZMod.val (1 : ZMod 2) = 1 from by decide, pow_one, hav, lw]
      · have hmem' : v ∈ L := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hav
          · exact h
        rw [ih (List.nodup_cons.mp hnd).2 hmem']
        rw [Pi.single_eq_of_ne hav, ZMod.val_zero, pow_zero, one_mul]

/-- `thetaFun` of a single generator indicator. -/
theorem thetaFun_single (n : ℕ) (v : Idx n) : thetaFun n (Pi.single v 1) = lw n v := by
  rw [thetaFun_eq]
  exact prod_delta n v (idxList n) (Finset.sort_nodup _ _)
    (by simp only [idxList, Finset.mem_sort, Finset.mem_univ])

/-! ## The four index permutations and the Jacobi computation -/

/-- `lw` of a triple of generators. -/
theorem lw_tuple (n : ℕ) (a b c : XX n) :
    lw n ![a, b, c] = mkQ n ⁅⁅FreeGroup.of a, FreeGroup.of b⁆, FreeGroup.of c⁆ := rfl

/-- Skew-symmetry in the first two slots, in coordinates. -/
theorem lw_swap_fst (n : ℕ) (a b c : XX n) : lw n ![b, a, c] = lw n ![a, b, c] := by
  rw [lw_tuple, lw_tuple]
  exact mkQ_commutator_swap n (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c)

/-- **The local Jacobi computation**: the product of the `lw`-classes over the four triples
`(a,b,c)`, `(b,a,c)`, `(c,a,b)`, `(c,b,a)` is the class of `(a,b,c)`. -/
theorem lw_prod_four (n : ℕ) (a b c : XX n) :
    lw n ![a, b, c] * lw n ![b, a, c] * lw n ![c, a, b] * lw n ![c, b, a]
      = lw n ![a, b, c] := by
  have hD : lw n ![c, b, a] = lw n ![b, c, a] := by
    rw [lw_tuple, lw_tuple]
    exact mkQ_commutator_swap n (FreeGroup.of b) (FreeGroup.of c) (FreeGroup.of a)
  have hJ : lw n ![a, b, c] * lw n ![b, c, a] * lw n ![c, a, b] = 1 := by
    rw [lw_tuple, lw_tuple, lw_tuple]
    exact mkQ_jacobi n (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c)
  have hA : lw n ![a, b, c] * lw n ![a, b, c] = 1 := lw_mul_self n ![a, b, c]
  have hC : lw n ![c, a, b] * lw n ![b, c, a] = lw n ![b, c, a] * lw n ![c, a, b] :=
    lw_mul_comm n ![c, a, b] ![b, c, a]
  rw [lw_swap_fst n a b c, hD]
  calc lw n ![a, b, c] * lw n ![a, b, c] * lw n ![c, a, b] * lw n ![b, c, a]
      = lw n ![c, a, b] * lw n ![b, c, a] := by rw [hA, one_mul]
    _ = lw n ![b, c, a] * lw n ![c, a, b] := hC
    _ = lw n ![a, b, c] := by
        have h1 : lw n ![a, b, c] * (lw n ![b, c, a] * lw n ![c, a, b]) = 1 := by
          rw [← mul_assoc]; exact hJ
        have h2 : lw n ![b, c, a] * lw n ![c, a, b] = (lw n ![a, b, c])⁻¹ :=
          eq_inv_of_mul_eq_one_right h1
        rw [h2, inv_eq_of_mul_eq_one_left hA]

theorem comp_id (n : ℕ) (v : Idx n) : (v ∘ ![0, 1, 2] : Idx n) = v := by
  funext i; fin_cases i <;> rfl

theorem comp_id_self (n : ℕ) (v : Idx n) : ((v ∘ ![0, 1, 2]) ∘ ![0, 1, 2] : Idx n) = v := by
  funext i; fin_cases i <;> rfl

theorem comp_s01_self (n : ℕ) (v : Idx n) : ((v ∘ ![1, 0, 2]) ∘ ![1, 0, 2] : Idx n) = v := by
  funext i; fin_cases i <;> rfl

theorem comp_cyc_inv (n : ℕ) (v : Idx n) : ((v ∘ ![1, 2, 0]) ∘ ![2, 0, 1] : Idx n) = v := by
  funext i; fin_cases i <;> rfl

theorem comp_inv_cyc (n : ℕ) (v : Idx n) : ((v ∘ ![2, 0, 1]) ∘ ![1, 2, 0] : Idx n) = v := by
  funext i; fin_cases i <;> rfl

theorem comp_s02_self (n : ℕ) (v : Idx n) : ((v ∘ ![2, 1, 0]) ∘ ![2, 1, 0] : Idx n) = v := by
  funext i; fin_cases i <;> rfl

theorem comp_eq_iff (n : ℕ) (s s' : Fin 3 → Fin 3)
    (h1 : ∀ v : Idx n, (v ∘ s) ∘ s' = v) (h2 : ∀ v : Idx n, (v ∘ s') ∘ s = v)
    (v w : Idx n) : v ∘ s = w ↔ v = w ∘ s' := by
  constructor
  · intro h; rw [← h1 v, h]
  · intro h; rw [h, h2 w]

/-- The list of the four inverse index permutations. -/
def lamPinvList : List (Fin 3 → Fin 3) := [![0, 1, 2], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]]

/-- `Λ` of an indicator function is the sum of the four indicators of the permuted tuples. -/
theorem LamT_single_eq (n : ℕ) (w : Idx n) :
    LamT n (Pi.single w 1) = (lamPinvList.map (fun q => Pi.single (w ∘ q) 1)).sum := by
  funext v
  rw [LamT_eq_sum, list_sum_apply]
  simp only [lamPinvList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Pi.single_apply, sw01, swcyc, sw02]
  rw [show lamP = insert ![0, 1, 2] (insert ![1, 0, 2] (insert ![1, 2, 0] {![2, 1, 0]}))
    from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [← comp_eq_iff n ![0, 1, 2] ![0, 1, 2] (comp_id_self n) (comp_id_self n),
    ← comp_eq_iff n ![1, 0, 2] ![1, 0, 2] (comp_s01_self n) (comp_s01_self n),
    ← comp_eq_iff n ![1, 2, 0] ![2, 0, 1] (comp_cyc_inv n) (comp_inv_cyc n),
    ← comp_eq_iff n ![2, 1, 0] ![2, 1, 0] (comp_s02_self n) (comp_s02_self n)]
  ring

/-- **The local `Λ`-invariance**: `thetaFun (Λ δ_w) = lw w`. -/
theorem thetaFun_Lam_single (n : ℕ) (w : Idx n) :
    thetaFun n (LamT n (Pi.single w 1)) = lw n w := by
  rw [LamT_single_eq, thetaFun_listSum, List.map_map]
  rw [show (lamPinvList.map (thetaFun n ∘ fun q => Pi.single (w ∘ q) 1))
      = lamPinvList.map (fun q => lw n (w ∘ q)) from by
    apply List.map_congr_left
    intro q _
    exact thetaFun_single n (w ∘ q)]
  simp only [lamPinvList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show (w ∘ ![0, 1, 2] : Idx n) = w from comp_id n w]
  rw [show (w ∘ ![1, 0, 2] : Idx n) = ![w 1, w 0, w 2] from by funext i; fin_cases i <;> rfl]
  rw [show (w ∘ ![2, 0, 1] : Idx n) = ![w 2, w 0, w 1] from by funext i; fin_cases i <;> rfl]
  rw [show (w ∘ ![2, 1, 0] : Idx n) = ![w 2, w 1, w 0] from by funext i; fin_cases i <;> rfl]
  rw [show (w : Idx n) = ![w 0, w 1, w 2] from by funext i; fin_cases i <;> rfl]
  exact lw_prod_four n (w 0) (w 1) (w 2)

/-! ## The global `Λ`-invariance -/

theorem thetaFun_LamT_aux (n : ℕ) (L : List (Idx n)) :
    ∀ g : TT n, (∀ w, w ∉ L → g w = 0) → thetaFun n (LamT n g) = thetaFun n g := by
  induction L with
  | nil =>
      intro g hg
      have hg0 : g = 0 := by funext w; exact hg w (by simp)
      rw [hg0, LamT_zero, thetaFun_zero']
  | cons u L ih =>
      intro g hg
      set g' : TT n := g - (g u) • (Pi.single u 1) with hg'def
      have hgsupp : ∀ w, w ∉ L → g' w = 0 := by
        intro w hw
        by_cases hwu : w = u
        · rw [hg'def, Pi.sub_apply, Pi.smul_apply, hwu, Pi.single_eq_same, smul_eq_mul, mul_one,
            sub_self]
        · have hg0 : g w = 0 := hg w (by simp [hwu, hw])
          rw [hg'def, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hwu, smul_zero, sub_zero,
            hg0]
      have hsplit : g = (g u) • (Pi.single u 1) + g' := by
        funext w
        simp only [hg'def, Pi.add_apply, Pi.sub_apply]
        abel
      rw [hsplit, LamT_add, thetaFun_add, LamT_smul, thetaFun_smul, thetaFun_Lam_single,
        ih g' hgsupp, thetaFun_add, thetaFun_smul, thetaFun_single]

/-- **`Λ`-invariance of `thetaFun`.** -/
theorem thetaFun_LamT (n : ℕ) (g : TT n) : thetaFun n (LamT n g) = thetaFun n g :=
  thetaFun_LamT_aux n (idxList n) g (by
    intro w hw
    exact absurd (by simp only [idxList, Finset.mem_sort, Finset.mem_univ] : w ∈ idxList n) hw)

end Work.SSGRoute.zz3
