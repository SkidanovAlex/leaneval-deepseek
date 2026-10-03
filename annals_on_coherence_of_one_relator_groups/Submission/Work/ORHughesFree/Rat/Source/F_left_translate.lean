import Mathlib
import Submission.Work.ORHughesFree.Rat.Source.Setup
import Submission.Work.ORHughesFree.RatU.ofGroup_ratOp_conj
import Submission.Work.ORHughesFree.RatU.conj_mul_identity

/-!
# Left translation of the source family `Rat.F`

For `a : U` and `x : Rat(U)` the family of subgroups `V` with `ofGroup a * x ∈ Rat(V)·U` is the
family of `V` such that `V.map (MulAut.conj a⁻¹) ∈ Rat.F x`:

  `Rat.F (ofGroup a * x) = { V | V.map (MulAut.conj a⁻¹) ∈ Rat.F x }`.

The proof reduces to two pointwise statements intertwining the `A`-families `Rat.A V` under
conjugation by `ofGroup g`:

* (descent) `ofGroup g * x * ofGroup g⁻¹ ∈ Rat.A V` implies
  `x ∈ Rat.A (V.map (MulAut.conj g⁻¹))`;
* (ascent) `x ∈ Rat.A (V.map (MulAut.conj g⁻¹))` implies
  `ofGroup g * x * ofGroup g⁻¹ ∈ Rat.A V`.

Both are proved by transporting a term along the bijection `u ↦ g * u * g⁻¹` of `U`, using the
term characterization `Rat.mem_A_iff` of `Rat.A` and the lemmas `Rat.supp_map_mem`,
`RatU.ofGroup_ratOp_conj` (for the `⋄`-clause of the term induction).
-/

namespace Work.ORHughesFree.Rat.Source

open Work.ORHughesFree

/-! ## Elementary identities -/

private theorem ofGroup_mul_self_inv {U : Type} [Group U] (g : U) :
    RatU.ofGroup g * RatU.ofGroup (g⁻¹) = (1 : RatU U) := by
  rw [← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one]

private theorem ofGroup_inv_mul_self {U : Type} [Group U] (g : U) :
    RatU.ofGroup (g⁻¹) * RatU.ofGroup g = (1 : RatU U) := by
  rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one]

/-- Conjugation by `ofGroup g⁻¹` undoes conjugation by `ofGroup g`. -/
private theorem ofGroup_inv_conj_cancel {U : Type} [Group U] (g : U) (z : RatU U) :
    RatU.ofGroup (g⁻¹) * (RatU.ofGroup g * z * RatU.ofGroup (g⁻¹))
      * RatU.ofGroup ((g⁻¹)⁻¹) = z := by
  have h1 : RatU.ofGroup (g⁻¹) * RatU.ofGroup g = (1 : RatU U) := ofGroup_inv_mul_self g
  rw [inv_inv]
  calc RatU.ofGroup (g⁻¹) * (RatU.ofGroup g * z * RatU.ofGroup (g⁻¹)) * RatU.ofGroup g
      = (RatU.ofGroup (g⁻¹) * RatU.ofGroup g) * z
          * (RatU.ofGroup (g⁻¹) * RatU.ofGroup g) := by noncomm_ring
    _ = 1 * z * 1 := by rw [h1]
    _ = z := by rw [one_mul, mul_one]

/-! ## Conjugation of a term

The conjugate of a term `t` by `g` is obtained by applying `u ↦ g * u * g⁻¹` to every group
element occurring in `t`; its value is the conjugate of the value of `t`. -/

private theorem mk_map_conj {U : Type} [Group U] (g : U) (t : RTerm U) :
    RatU.mk (RTerm.map (fun u => g * u * g⁻¹) t)
      = RatU.ofGroup g * RatU.mk t * RatU.ofGroup (g⁻¹) := by
  have hgg : RatU.ofGroup (g⁻¹) * RatU.ofGroup g = (1 : RatU U) := ofGroup_inv_mul_self g
  induction t with
  | z => simp only [RTerm.map, RatU.mk_zero, mul_zero, zero_mul]
  | o =>
    simp only [RTerm.map, RatU.mk_one]
    rw [mul_one, ofGroup_mul_self_inv]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [RTerm.map, RatU.mk_add]
    rw [ih₁, ih₂, mul_add, add_mul]
  | mul t₁ t₂ ih₁ ih₂ =>
    simp only [RTerm.map, RatU.mk_mul]
    rw [ih₁, ih₂, ← RatU.conj_mul_identity (RatU.ofGroup g) (RatU.ofGroup (g⁻¹)) hgg]
  | rat t₁ ih₁ =>
    simp only [RTerm.map, RatU.mk_rat]
    rw [ih₁]
    simpa only [zpow_one, zpow_neg_one] using
      (RatU.ofGroup_ratOp_conj g 1 (RatU.mk t₁)).symm
  | smulL u t₁ ih₁ =>
    simp only [RTerm.map, RatU.mk_smulL]
    rw [ih₁]
    simp only [RatU.smul_eq_ofGroup_mul, RatU.ofGroup_mul]
    rw [← RatU.conj_mul_identity (RatU.ofGroup g) (RatU.ofGroup (g⁻¹)) hgg]
  | smulR u t₁ ih₁ =>
    simp only [RTerm.map, RatU.mk_smulR]
    rw [ih₁]
    simp only [RatU.smulRight_eq_mul_ofGroup, RatU.ofGroup_mul]
    rw [← RatU.conj_mul_identity (RatU.ofGroup g) (RatU.ofGroup (g⁻¹)) hgg]

/-! ## The two pointwise statements -/

/-- Membership in a conjugate subgroup, by the inverse conjugation. -/
private theorem mem_map_conj_iff {U : Type} [Group U] (V : Subgroup U) (g u : U) :
    u ∈ V.map (MulAut.conj g) ↔ g⁻¹ * u * g ∈ V := by
  have h := Subgroup.mem_map_equiv (K := V) (x := u) (f := MulAut.conj g)
  rw [MulAut.conj_symm_apply] at h
  exact h

/-- **Descent.** If `ofGroup g * x * ofGroup g⁻¹ ∈ Rat.A V`, then
`x ∈ Rat.A (V.map (MulAut.conj g⁻¹))`. -/
private theorem mem_A_map_conj_inv {U : Type} [Group U] (g : U) (V : Subgroup U) (x : RatU U)
    (hx : RatU.ofGroup g * x * RatU.ofGroup (g⁻¹) ∈ Rat.A V) :
    x ∈ Rat.A (V.map (MulAut.conj g⁻¹)) := by
  rw [Rat.mem_A_iff] at hx ⊢
  obtain ⟨t, ht, htmk⟩ := hx
  refine ⟨RTerm.map (fun u => g⁻¹ * u * (g⁻¹)⁻¹) t, ?_, ?_⟩
  · intro u' hu'
    obtain ⟨u, hu, hfu⟩ := Rat.supp_map_mem (fun u => g⁻¹ * u * (g⁻¹)⁻¹) t hu'
    rw [mem_map_conj_iff, inv_inv]
    have h : g * u' * g⁻¹ = u := by rw [← hfu]; group
    rw [h]
    exact ht u hu
  · rw [mk_map_conj (g⁻¹) t, htmk]
    exact ofGroup_inv_conj_cancel g x

/-- **Ascent.** If `x ∈ Rat.A (V.map (MulAut.conj g⁻¹))`, then
`ofGroup g * x * ofGroup g⁻¹ ∈ Rat.A V`. -/
private theorem mem_A_conj_of_mem_map_conj_inv {U : Type} [Group U] (g : U) (V : Subgroup U)
    (x : RatU U) (hx : x ∈ Rat.A (V.map (MulAut.conj g⁻¹))) :
    RatU.ofGroup g * x * RatU.ofGroup (g⁻¹) ∈ Rat.A V := by
  rw [Rat.mem_A_iff] at hx ⊢
  obtain ⟨t, ht, htmk⟩ := hx
  refine ⟨RTerm.map (fun u => g * u * g⁻¹) t, ?_, ?_⟩
  · intro u' hu'
    obtain ⟨u, hu, hfu⟩ := Rat.supp_map_mem (fun u => g * u * g⁻¹) t hu'
    have huV : u ∈ V.map (MulAut.conj g⁻¹) := ht u hu
    rw [mem_map_conj_iff, inv_inv] at huV
    rw [hfu.symm]
    exact huV
  · rw [mk_map_conj g t, htmk]

/-! ## The translation by a group element on the left -/

/-- `ofGroup a * (z * ofGroup (u * a)) * ofGroup a⁻¹ = ofGroup a * z * ofGroup u`. -/
private theorem mul_conj_ofGroup_mul {U : Type} [Group U] (a : U) (z : RatU U) (u : U) :
    RatU.ofGroup a * (z * RatU.ofGroup (u * a)) * RatU.ofGroup (a⁻¹)
      = RatU.ofGroup a * z * RatU.ofGroup u := by
  rw [RatU.ofGroup_mul]
  rw [show RatU.ofGroup a * (z * (RatU.ofGroup u * RatU.ofGroup a)) * RatU.ofGroup (a⁻¹)
      = (RatU.ofGroup a * z * RatU.ofGroup u) * (RatU.ofGroup a * RatU.ofGroup (a⁻¹)) from
        by noncomm_ring]
  rw [ofGroup_mul_self_inv, mul_one]

/-- `ofGroup a * (z * ofGroup u) * ofGroup a⁻¹ = ofGroup a * z * ofGroup (u * a⁻¹)`. -/
private theorem mul_conj_ofGroup_mul_eq {U : Type} [Group U] (a : U) (z : RatU U) (u : U) :
    RatU.ofGroup a * (z * RatU.ofGroup u) * RatU.ofGroup (a⁻¹)
      = RatU.ofGroup a * z * RatU.ofGroup (u * a⁻¹) := by
  rw [RatU.ofGroup_mul]
  noncomm_ring

theorem F_left_translate {U : Type} [Group U] (a : U) (x : Work.ORHughesFree.RatU U) :
    Work.ORHughesFree.Rat.F (Work.ORHughesFree.RatU.ofGroup a * x) =
      { V : Subgroup U | V.map (MulAut.conj a⁻¹) ∈ Work.ORHughesFree.Rat.F x } := by
  ext P
  rw [Set.mem_ofPred_eq, Rat.mem_F_iff', Rat.mem_F_iff']
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u * a, ?_⟩
    refine mem_A_map_conj_inv a P (x * RatU.ofGroup (u * a)) ?_
    rw [mul_conj_ofGroup_mul a x u]
    exact hu
  · rintro ⟨u, hu⟩
    refine ⟨u * a⁻¹, ?_⟩
    rw [← mul_conj_ofGroup_mul_eq a x u]
    exact mem_A_conj_of_mem_map_conj_inv a P (x * RatU.ofGroup u) hu

end Work.ORHughesFree.Rat.Source
