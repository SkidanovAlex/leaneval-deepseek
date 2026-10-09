import Mathlib
import Submission.Work.SSGRoute.zz3.Defs
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.adjacent_pSeries_inter_lcs_le
import Submission.Work.SSGRoute.wtz_filz_exists_pow
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.oneStep.magLead_pSeries_divisible
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-`3` Magnus coefficient functional on `γ₃ ⊂ F(n)`

This file sets up the tool with which `Work.SSGRoute.zz3.ThetaKer` is proved: the mod-`2` degree-`3`
coefficient of the Magnus image, evaluated on `γ₃ = F(n).lowerCentralSeries 2`.

For `x ∈ γ₃` the Magnus image `M(x)` has no components of degree `< 3`, whence the degree-`3`
component of `M(x) - 1` is additive on `γ₃`.  Passing to the degree-`3` part of the truncation at
`fil 4`, every coefficient is the value of a `ℤ/2`-valued additive functional `lamCoeff n W`.

The structural facts proved downstream are

* `lamCoeff_eq_zero_of_mem_pSeries4` : vanishing on `γ₃ ∩ P₄` (so that `lamCoeff` descends to the
  graded piece `F^{(3,3)}/F^{(4,1)}`), and
* `lamCoeff_lc` : its value on the left-nested commutator of a triple of generators.
-/

open scoped commutatorElement
open Work.CohomologicalShrinking
open Work.SSGRoute.ZZ3
attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.SSGRoute.zz3

/-- `F(n) = FreeGroup (Fin n × Gm)`. -/
abbrev FFn (n : ℕ) : Type := Work.Shrinking.freeOperatorGroup Gm n

/-- `γ₃` of `F(n)`, Mathlib indexing `lowerCentralSeries 2`. -/
abbrev Gam3 (n : ℕ) : Subgroup (FFn n) := (⊤ : Subgroup (FFn n)).lowerCentralSeries 2

/-- The free associative algebra over `ℤ` on the generators `XX n`. -/
abbrev AA (n : ℕ) : Type := Work.SSGRoute.prop5.FreeAssoc (XX n)

/-! ## The quotient map `mkQ` and the term `P₄ = F(n)^{(4,1)}` -/

theorem mkQ_one' (n : ℕ) : mkQ n (1 : FFn n) = 1 := by
  show QuotientGroup.mk' _ (⟨1, Subgroup.mem_top 1⟩ : ↥(⊤ : Subgroup (FFn n))) = 1
  rw [show (⟨1, Subgroup.mem_top (1 : FFn n)⟩ : ↥(⊤ : Subgroup (FFn n))) = 1 from
    Subtype.ext rfl, map_one]

theorem mkQ_mul' (n : ℕ) (a b : FFn n) : mkQ n (a * b) = mkQ n a * mkQ n b := by
  show QuotientGroup.mk' _ (⟨a * b, Subgroup.mem_top (a * b)⟩ :
      ↥(⊤ : Subgroup (FFn n))) = _
  rw [show (⟨a * b, Subgroup.mem_top (a * b)⟩ : ↥(⊤ : Subgroup (FFn n))) =
      (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (FFn n))) *
      (⟨b, Subgroup.mem_top b⟩ : ↥(⊤ : Subgroup (FFn n))) from Subtype.ext rfl, map_mul]
  rfl

theorem mkQ_pow' (n : ℕ) (a : FFn n) (k : ℕ) : mkQ n (a ^ k) = (mkQ n a) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mkQ_one']
  | succ k ih => rw [pow_succ, pow_succ, mkQ_mul', ih]

theorem mkQ_eq_one_iff' (n : ℕ) (a : FFn n) :
    mkQ n a = 1 ↔ a ∈ flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 := by
  show QuotientGroup.mk' _ (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (FFn n))) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Iff.rfl

/-- `F(n)^{(4,1)} = P₄ = F(n).lowerCentralSeries (3-1)`... precisely `pCentralSeries 2 (F n) 3`. -/
theorem flowTerm_four_one' (n : ℕ) :
    flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2
      = Work.Shrinking.pCentralSeries 2 (FFn n) 3 := by
  show refinedTerm 2 (FFn n) 4 1 = Work.Shrinking.pCentralSeries 2 (FFn n) 3
  have h1 : centralSeries (FFn n) 1 = ⊤ := rfl
  have h2 : pSeries 2 (FFn n) 4 = Work.Shrinking.pCentralSeries 2 (FFn n) 3 := rfl
  have h3 : Work.Shrinking.pCentralSeries 2 (FFn n) 4 ≤ Work.Shrinking.pCentralSeries 2 (FFn n) 3 :=
    Work.Shrinking.pCentralSeries_antitone 2 (FFn n) (by norm_num)
  simp only [refinedTerm, h1, inf_top_eq, h2]
  exact sup_eq_left.mpr h3

/-! ## The degree-`3` part of the Magnus image -/

/-- A lift of the class `magLead 4 x ∈ filq (XX n) 4 3` to `fil (XX n) 3`, for `x ∈ γ₃`. -/
noncomputable def mag3Lift (n : ℕ) (x : FFn n) (hx : x ∈ Gam3 n) : AA n :=
  Classical.choose ((Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4))
    Ideal.Quotient.mk_surjective).1
    (Work.SSGRoute.prop5.magLead_mem_filq (X := XX n) 4 3 (by norm_num) (by norm_num) hx))

theorem mag3Lift_mem (n : ℕ) (x : FFn n) (hx : x ∈ Gam3 n) :
    mag3Lift n x hx ∈ Work.SSGRoute.prop5.fil (XX n) 3 :=
  (Classical.choose_spec ((Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4))
    Ideal.Quotient.mk_surjective).1
    (Work.SSGRoute.prop5.magLead_mem_filq (X := XX n) 4 3 (by norm_num) (by norm_num) hx))).1

theorem mag3Lift_mk (n : ℕ) (x : FFn n) (hx : x ∈ Gam3 n) :
    Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4) (mag3Lift n x hx)
      = Work.SSGRoute.prop5.magLead (X := XX n) 4 x :=
  (Classical.choose_spec ((Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4))
    Ideal.Quotient.mk_surjective).1
    (Work.SSGRoute.prop5.magLead_mem_filq (X := XX n) 4 3 (by norm_num) (by norm_num) hx))).2

/-- A coefficient of `fil (XX n) N` at a word of length `< N` vanishes. -/
theorem coeff_eq_zero_of_mem_fil {n N : ℕ} {a : AA n} (ha : a ∈ Work.SSGRoute.prop5.fil (XX n) N)
    {w : FreeMonoid (XX n)} (hw : w.length < N) : a.coeff w = 0 := by
  by_contra hne
  have hz : a ∈ Work.SSGRoute.prop5.filz (XX n) N :=
    Work.SSGRoute.prop5.fil_le_filz (XX n) N ha
  exact absurd (Work.SSGRoute.prop5.mem_filz_iff.mp hz w hne) (by omega)

/-- **The degree-`3` Magnus coefficient functional** (mod `2`): the coefficient of the word `W` in
the degree-`3` part of the Magnus image of `x`, for `x ∈ γ₃` (and `0` otherwise). -/
noncomputable def lamCoeff (n : ℕ) (W : FreeMonoid (XX n)) (x : FFn n) : ZMod 2 :=
  if h : x ∈ Gam3 n then ((mag3Lift n x h).coeff W : ZMod 2) else 0

theorem lamCoeff_of_mem {n : ℕ} {W : FreeMonoid (XX n)} {x : FFn n} (h : x ∈ Gam3 n) :
    lamCoeff n W x = ((mag3Lift n x h).coeff W : ZMod 2) := dif_pos h

/-- `lamCoeff` evaluated through any lift of the Magnus class. -/
theorem lamCoeff_apply_lift (n : ℕ) (W : FreeMonoid (XX n)) (hW : W.length = 3) {x : FFn n}
    (hx : x ∈ Gam3 n) {a : AA n}
    (ha : Work.SSGRoute.prop5.magLead (X := XX n) 4 x
        = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4) a) :
    lamCoeff n W x = (a.coeff W : ZMod 2) := by
  rw [lamCoeff_of_mem hx]
  have hsub : a - mag3Lift n x hx ∈ Work.SSGRoute.prop5.fil (XX n) 4 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ha, mag3Lift_mk, sub_self]
  have h0 : (a - mag3Lift n x hx).coeff W = 0 :=
    coeff_eq_zero_of_mem_fil hsub (by rw [hW]; norm_num)
  rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply] at h0
  have h1 : (a.coeff W : ZMod 2) = ((mag3Lift n x hx).coeff W : ZMod 2) := by
    have : (a.coeff W : ZMod 2) - ((mag3Lift n x hx).coeff W : ZMod 2) = 0 := by
      rw [← Int.cast_sub, h0, Int.cast_zero]
    exact sub_eq_zero.mp this
  exact h1.symm

/-- The value of `lamCoeff` on the identity vanishes. -/
theorem lamCoeff_one (n : ℕ) (W : FreeMonoid (XX n)) (hW : W.length = 3) :
    lamCoeff n W 1 = 0 := by
  have hmem : (1 : FFn n) ∈ Gam3 n := (Gam3 n).one_mem
  rw [lamCoeff_apply_lift n W hW hmem (a := 0) (by rw [Work.SSGRoute.prop5.magLead_one, map_zero])]
  simp

/-- **Additivity of `lamCoeff` on `γ₃`.** -/
theorem lamCoeff_add (n : ℕ) (W : FreeMonoid (XX n)) (hW : W.length = 3) (x y : FFn n)
    (hx : x ∈ Gam3 n) (hy : y ∈ Gam3 n) :
    lamCoeff n W (x * y) = lamCoeff n W x + lamCoeff n W y := by
  have hkey : Work.SSGRoute.prop5.magLead (X := XX n) 4 (x * y)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4)
          (mag3Lift n x hx + mag3Lift n y hy) := by
    rw [Work.SSGRoute.prop5.magLead_mul (X := XX n) 4 3 (by norm_num) (by norm_num) (by norm_num)
        hx hy,
      map_add, mag3Lift_mk, mag3Lift_mk]
  rw [lamCoeff_apply_lift n W hW ((Gam3 n).mul_mem hx hy) hkey,
    lamCoeff_apply_lift n W hW hx (mag3Lift_mk n x hx).symm,
    lamCoeff_apply_lift n W hW hy (mag3Lift_mk n y hy).symm,
    MonoidAlgebra.coeff_add, Finsupp.add_apply, Int.cast_add]

/-- `lamCoeff` of a power. -/
theorem lamCoeff_pow (n : ℕ) (W : FreeMonoid (XX n)) (hW : W.length = 3) (x : FFn n)
    (hx : x ∈ Gam3 n) (k : ℕ) :
    lamCoeff n W (x ^ k) = (k : ZMod 2) * lamCoeff n W x := by
  have hkey : Work.SSGRoute.prop5.magLead (X := XX n) 4 (x ^ k)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4)
          ((k : ℤ) • mag3Lift n x hx) := by
    rw [Work.SSGRoute.prop5.magLead_pow (X := XX n) 4 3 k (by norm_num) (by norm_num)
        (by norm_num) hx]
    rw [show Work.SSGRoute.prop5.magLead (X := XX n) 4 x
        = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4) (mag3Lift n x hx)
        from (mag3Lift_mk n x hx).symm]
    rw [zsmul_eq_mul, map_mul, map_intCast]
  rw [lamCoeff_apply_lift n W hW ((Gam3 n).pow_mem hx k) hkey,
    lamCoeff_apply_lift n W hW hx (mag3Lift_mk n x hx).symm,
    MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]

/-- `lamCoeff` of a product of elements of `γ₃` is the sum of the values. -/
theorem lamCoeff_listProd (n : ℕ) (W : FreeMonoid (XX n)) (hW : W.length = 3) :
    ∀ (L : List (FFn n)), (∀ x ∈ L, x ∈ Gam3 n) →
      lamCoeff n W L.prod = (L.map (fun x => lamCoeff n W x)).sum := by
  intro L
  induction L with
  | nil => intro _; rw [List.prod_nil, List.map_nil, List.sum_nil]; exact lamCoeff_one n W hW
  | cons a L ih =>
      intro hL
      have ha : a ∈ Gam3 n := hL a List.mem_cons_self
      have hL' : ∀ x ∈ L, x ∈ Gam3 n := fun x hx => hL x (List.mem_cons_of_mem a hx)
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        lamCoeff_add n W hW a L.prod ha (Subgroup.list_prod_mem (Gam3 n) hL'), ih hL']

/-- The left-nested commutator of a triple of generators lies in `γ₃`. -/
theorem lcF_mem_gam3 (n : ℕ) (u : Fin 3 → XX n) : lcF n u ∈ Gam3 n := by
  have hlc : lcF n u = ⁅⁅FreeGroup.of (u 0), FreeGroup.of (u 1)⁆, FreeGroup.of (u 2)⁆ := by
    show Work.SSGRoute.prop5.lc (List.ofFn u) = _
    simp [Work.SSGRoute.prop5.lc, List.ofFn_succ, List.ofFn_zero]
  rw [hlc]
  exact Work.SSGRoute.prop5.commutator_lowerCentralSeries_le (FFn n) 1 0
    (Subgroup.commutator_mem_commutator
      (Work.SSGRoute.prop5.commutator_lowerCentralSeries_le (FFn n) 0 0
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)))
      (Subgroup.mem_top _))


/-! ## The value of `lamCoeff` on a left-nested commutator of a triple of generators -/

/-- `FreeMonoid.ofList` is injective. -/
lemma ofList_inj {α : Type*} (s t : List α) :
    FreeMonoid.ofList s = FreeMonoid.ofList t ↔ s = t := by
  constructor
  · intro h; rw [← FreeMonoid.toList_ofList s, h, FreeMonoid.toList_ofList t]
  · intro h; rw [h]

lemma wordEl_append {X : Type*} (s t : List X) :
    Work.SSGRoute.prop5.wordEl (s ++ t)
      = Work.SSGRoute.prop5.wordEl s * Work.SSGRoute.prop5.wordEl t := by
  rw [Work.SSGRoute.prop5.wordEl, Work.SSGRoute.prop5.wordEl, Work.SSGRoute.prop5.wordEl,
    FreeMonoid.ofList_append, MonoidAlgebra.single_mul_single, mul_one]

lemma wordEl_three {X : Type*} (x y z : X) :
    Work.SSGRoute.prop5.wordEl [x, y, z]
      = Work.SSGRoute.prop5.wordEl [x] * Work.SSGRoute.prop5.wordEl [y]
        * Work.SSGRoute.prop5.wordEl [z] := by
  have h : ([x, y, z] : List X) = [x] ++ ([y] ++ [z]) := rfl
  rw [h, wordEl_append, wordEl_append, mul_assoc]

lemma lnMon_three {X : Type*} (x y z : X) :
    Work.SSGRoute.prop5.lnMon [x, y, z]
      = Work.SSGRoute.prop5.wordEl [x, y, z] - Work.SSGRoute.prop5.wordEl [y, x, z]
        - Work.SSGRoute.prop5.wordEl [z, x, y] + Work.SSGRoute.prop5.wordEl [z, y, x] := by
  simp only [Work.SSGRoute.prop5.lnMon, List.foldl_cons, List.foldl_nil]
  rw [wordEl_three x y z, wordEl_three y x z, wordEl_three z x y, wordEl_three z y x]
  noncomm_ring

lemma coeff_lnMon_three {X : Type*} (x y z : X) (v : FreeMonoid X) :
    (Work.SSGRoute.prop5.lnMon [x, y, z]).coeff v
      = (if v = FreeMonoid.ofList [x, y, z] then (1:ℤ) else 0)
        - (if v = FreeMonoid.ofList [y, x, z] then 1 else 0)
        - (if v = FreeMonoid.ofList [z, x, y] then 1 else 0)
        + (if v = FreeMonoid.ofList [z, y, x] then 1 else 0) := by
  have h := congrArg (fun a : Work.SSGRoute.prop5.FreeAssoc X => a.coeff v) (lnMon_three x y z)
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_sub, Finsupp.add_apply,
    Finsupp.sub_apply, Work.SSGRoute.prop5.wordEl, Work.SSGRoute.prop5.coeff_single_fa] at h
  exact h

/-- The inverse three-cycle, as an index permutation. -/
def scInv : Fin 3 → Fin 3 := ![2, 0, 1]

lemma comp_invol_iff {α β : Type*} (σ : α → α) (hσ : ∀ i, σ (σ i) = i) (u W : α → β) :
    (W = fun i => u (σ i)) ↔ (u = fun i => W (σ i)) := by
  constructor
  · intro h; funext i
    have h2 := congrFun h (σ i)
    simp only [hσ i] at h2
    exact h2.symm
  · intro h; funext i
    rw [h]
    simp only [hσ i]

lemma comp_inv_iff {α β : Type*} (σ γ : α → α) (h1 : ∀ i, σ (γ i) = i)
    (h2 : ∀ i, γ (σ i) = i) (u W : α → β) : (W = fun i => u (γ i)) ↔ (u = fun i => W (σ i)) := by
  constructor
  · intro h; funext i
    have h2' := congrFun h (σ i)
    simp only [h2 i] at h2'
    exact h2'.symm
  · intro h; funext i
    rw [h]
    simp only [h1 i]

/-- **The value of `lamCoeff` on the left-nested commutator of a triple of generators.** -/
theorem lamCoeff_lc (n : ℕ) (W u : Fin 3 → XX n) :
    lamCoeff n (FreeMonoid.ofList (List.ofFn W)) (lcF n u)
      = (if u = W then 1 else 0) + (if u = (fun i => W (sw01 i)) then 1 else 0)
        + (if u = (fun i => W (swcyc i)) then 1 else 0)
        + (if u = (fun i => W (sw02 i)) then 1 else 0) := by
  have hfu : List.ofFn u = [u 0, u 1, u 2] := by simp [List.ofFn_succ, List.ofFn_zero]
  have hfW : List.ofFn W = [W 0, W 1, W 2] := by simp [List.ofFn_succ, List.ofFn_zero]
  have hWlen : (FreeMonoid.ofList (List.ofFn W)).length = 3 := by
    rw [show (FreeMonoid.ofList (List.ofFn W)).length
        = (FreeMonoid.toList (FreeMonoid.ofList (List.ofFn W))).length from rfl,
      FreeMonoid.toList_ofList]
    simp [List.ofFn_succ, List.ofFn_zero]
  have hmem : lcF n u ∈ Gam3 n := lcF_mem_gam3 n u
  have hkey : Work.SSGRoute.prop5.magLead (X := XX n) 4 (lcF n u)
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4)
          (Work.SSGRoute.prop5.lnMon (List.ofFn u)) := by
    have h := Work.SSGRoute.prop5.magLead_lc_congr (X := XX n) 4 (w := List.ofFn u)
      (by simp) (by simp)
    rw [show (List.ofFn u).length + 1 = 4 from by simp,
      Work.SSGRoute.prop5.filq_self_eq_bot' (X := XX n) 4, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  rw [lamCoeff_apply_lift n (FreeMonoid.ofList (List.ofFn W)) hWlen hmem hkey,
    hfu, congrArg FreeMonoid.ofList hfW, coeff_lnMon_three]
  rw [Int.cast_add, Int.cast_sub, Int.cast_sub]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]
  have hlist2 : ([u 1, u 0, u 2] : List (XX n))
      = List.ofFn (fun i => u (sw01 i)) := rfl
  have hlist3 : ([u 2, u 0, u 1] : List (XX n))
      = List.ofFn (fun i => u (scInv i)) := rfl
  have hlist4 : ([u 2, u 1, u 0] : List (XX n))
      = List.ofFn (fun i => u (sw02 i)) := rfl
  have hiff1 : ((FreeMonoid.ofList [W 0, W 1, W 2] : FreeMonoid (XX n))
        = FreeMonoid.ofList [u 0, u 1, u 2]) ↔ (u = W) := by
    rw [ofList_inj, ← hfW, ← hfu, List.ofFn_inj, eq_comm]
  have hiff2 : ((FreeMonoid.ofList [W 0, W 1, W 2] : FreeMonoid (XX n))
        = FreeMonoid.ofList [u 1, u 0, u 2]) ↔ (u = (fun i => W (sw01 i))) := by
    rw [ofList_inj, ← hfW, hlist2, List.ofFn_inj,
      comp_invol_iff sw01 (fun i => by fin_cases i <;> rfl)]
  have hiff3 : ((FreeMonoid.ofList [W 0, W 1, W 2] : FreeMonoid (XX n))
        = FreeMonoid.ofList [u 2, u 0, u 1]) ↔ (u = (fun i => W (swcyc i))) := by
    rw [ofList_inj, ← hfW, hlist3, List.ofFn_inj,
      comp_inv_iff swcyc scInv (fun i => by fin_cases i <;> rfl)
        (fun i => by fin_cases i <;> rfl)]
  have hiff4 : ((FreeMonoid.ofList [W 0, W 1, W 2] : FreeMonoid (XX n))
        = FreeMonoid.ofList [u 2, u 1, u 0]) ↔ (u = (fun i => W (sw02 i))) := by
    rw [ofList_inj, ← hfW, hlist4, List.ofFn_inj,
      comp_invol_iff sw02 (fun i => by fin_cases i <;> rfl)]
  simp only [hiff1, hiff2, hiff3, hiff4, CharTwo.sub_eq_add]


/-- **Vanishing of `lamCoeff` on `γ₃ ∩ P₄`.**  For `x ∈ γ₃ ∩ P₄` the Magnus leading term of `x` at
degree `3` is divisible by `2^(4-3) = 2`, so all its length-`3` coefficients are even. -/
theorem lamCoeff_eq_zero_of_mem_pSeries4 (n : ℕ) (W : FreeMonoid (XX n)) (hW : W.length = 3)
    (x : FFn n) (hx : x ∈ Gam3 n) (hx4 : x ∈ pSeries 2 (FFn n) 4) :
    lamCoeff n W x = 0 := by
  obtain ⟨a, _ha, haeq⟩ := Work.SSGRoute.oneStep.magLead_pSeries_divisible 2 (XX n) 4 3
    (by norm_num) (by norm_num) hx4 hx
  obtain ⟨a', _ha', ha'eq⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4))
    Ideal.Quotient.mk_surjective).1 _ha
  have hA : Work.SSGRoute.prop5.magLead (X := XX n) 4 x
      = Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4) (((2:ℤ)^(4-3)) • a') := by
    rw [haeq, ← ha'eq]
    exact (map_zsmul (Ideal.Quotient.mk (Work.SSGRoute.prop5.fil (XX n) 4))
      ((2:ℤ)^(4-3)) a').symm
  rw [lamCoeff_apply_lift n W hW hx hA]
  rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_pow]
  rw [show ((2:ℤ) : ZMod 2) = 0 from by decide]
  simp


/-- `mkQ` commutes with list products. -/
lemma mkQ_listProd (n : ℕ) (l : List (FFn n)) :
    mkQ n l.prod = (l.map (fun x => mkQ n x)).prod := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.prod_nil, mkQ_one']
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, mkQ_mul', ih]

/-- The indicator sum over `Idx n`: `∑ w, φ w * [w = y] = φ y`. -/
lemma sum_mul_ite_eq (n : ℕ) (φ : Idx n → ZMod 2) (y : Idx n) :
    (∑ w : Idx n, φ w * (if w = y then 1 else 0)) = φ y := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb; rw [if_neg hb, mul_zero]
  · intro hy; exact absurd (Finset.mem_univ y) hy

end Work.SSGRoute.zz3
