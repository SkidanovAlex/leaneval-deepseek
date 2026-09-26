import Submission.Work.RouteB.Ascend

open OnPropertyT Submission.Helpers Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Submission.RouteB

noncomputable section

/-!
# Property (T) ascends across an index-two extension (certificate form)

`ChallengeDeps.PropertyT G` is the *algebraic certificate* form of Kazhdan's
property (T): a finite symmetric generating set `S` with `closure S = ⊤`, a
`Λ > 0` and a finite family `ξ` of group-ring elements with
`Δ_S² - Λ • Δ_S = ∑ star ξ ξ`.  This file proves that the certificate ascends
from a subgroup to an index-two overgroup: if `γ ∈ G` is an involution with
`γ ∉ S`, normalising `S` in the sense `g * Δ_S * g = Δ_S` (where
`g = of γ`), and `S ∪ {γ}` still generates `G`, then a certificate for
`(S, Λ₀, ξ)` yields one for `G`.

This is the step which would deduce `Aut(F_n)` from `SAut(F_n)` in the
Kaluba–Kielak–Nowak route (index two, `γ` an involution normalising the
transvection generating set).

The construction: with `e := ½(1 - γ)` (idempotent) one has
`Δ_{S∪{γ}} = Δ_S + 2e`, so (using `Δ_S² = Λ₀Δ_S + ∑ξ*ξ`)
`Δ_{S∪{γ}}² - Λ•Δ_{S∪{γ}} = (∑ξ*ξ) + (Λ₀-Λ)•Δ_S + 4•(Δ_S·e) + (4-2Λ)•e`
for `Λ ≤ min Λ₀ 2`; each of the four summands is an explicit finite sum of
hermitian squares (`4·Δ_S·e = ½∑_{s∈S} star((1-s)(1-γ))((1-s)(1-γ))`, using
`γΔ_S = Δ_Sγ`), and `merge_sq_fintype` converts the resulting index-type sum
into the Finset form required by the definition.
-/

variable {G : Type*} [Group G]

/-- The group-ring element `of γ` of an involution is an involution. -/
lemma of_mul_self_of_involution (γ : G) (hγ : γ * γ = 1) :
    (MonoidAlgebra.of ℝ G γ) * (MonoidAlgebra.of ℝ G γ) = 1 := by
  rw [← map_mul, hγ, map_one]

/-- **`e := ½(1-γ)` is idempotent** for an involution `γ`. -/
lemma half_one_sub_idem (γ : G) (hγ : γ * γ = 1) :
    ((2:ℝ)⁻¹ • (1 - MonoidAlgebra.of ℝ G γ)) * ((2:ℝ)⁻¹ • (1 - MonoidAlgebra.of ℝ G γ))
      = (2:ℝ)⁻¹ • (1 - MonoidAlgebra.of ℝ G γ) := by
  have hg2 := of_mul_self_of_involution γ hγ
  rw [smul_mul_smul]
  rw [show (1 - MonoidAlgebra.of ℝ G γ) * (1 - MonoidAlgebra.of ℝ G γ)
        = (2:ℝ) • (1 - MonoidAlgebra.of ℝ G γ) by
      rw [sub_mul, one_mul, mul_sub, mul_one, hg2]
      rw [two_smul ℝ (1 - MonoidAlgebra.of ℝ G γ)]
      abel]
  rw [← smul_assoc]
  rw [show ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) • 2 = (2:ℝ)⁻¹ by norm_num]

/-- `γ` and `Δ_S` commute when `γ` normalises the Laplacian. -/
lemma of_comm_laplacian (S : Finset G) (γ : G) (hγ : γ * γ = 1)
    (hΔγ : MonoidAlgebra.of ℝ G γ * OnPropertyT.Laplacian S * MonoidAlgebra.of ℝ G γ
      = OnPropertyT.Laplacian S) :
    MonoidAlgebra.of ℝ G γ * OnPropertyT.Laplacian S = OnPropertyT.Laplacian S * MonoidAlgebra.of ℝ G γ := by
  have hg2 := of_mul_self_of_involution γ hγ
  have h := congrArg (fun z => z * MonoidAlgebra.of ℝ G γ) hΔγ
  simp only [mul_assoc] at h
  rw [hg2, mul_one] at h
  exact h


/-- **The Laplacian of `insert γ S`** in terms of `Δ_S` and `e = ½(1-γ)`:
`Δ_{insert γ S} = Δ_S + 2e`. -/
lemma laplacian_insert_eq {G : Type*} [Group G] [DecidableEq G] (S : Finset G) (γ : G)
    (hγS : γ ∉ S) :
    OnPropertyT.Laplacian (insert γ S) = OnPropertyT.Laplacian S
      + (2:ℝ) • ((2:ℝ)⁻¹ • (1 - MonoidAlgebra.of ℝ G γ)) := by
  unfold OnPropertyT.Laplacian
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Finset.card_insert_of_notMem hγS, Finset.sum_insert hγS]
  push_cast
  rw [show (2:ℝ) • ((2:ℝ)⁻¹ • (1 - MonoidAlgebra.of ℝ G γ))
        = 1 - MonoidAlgebra.of ℝ G γ from smul_inv_smul₀ two_ne_zero _]
  abel

/-- **Property (T) ascends across an index-two extension (certificate form).**
Let `S ⊆ G` be a finite symmetric set and `γ` an involution with `γ ∉ S` which
normalises the Laplacian of `S`; suppose `insert γ S` generates `G`.  Then a
property-(T) certificate for `(S, Λ₀, ξ)` yields one for `G` with generating set
`insert γ S` and `Λ = min Λ₀ 1`. -/
theorem propertyT_of_index_two_extension {G : Type*} [Group G] [DecidableEq G]
    (S : Finset G) (hsym : (S : Set G)⁻¹ = S) (γ : G) (hγ : γ * γ = 1) (hγS : γ ∉ S)
    (hΔγ : MonoidAlgebra.of ℝ G γ * OnPropertyT.Laplacian S * MonoidAlgebra.of ℝ G γ
      = OnPropertyT.Laplacian S)
    (hgen : Subgroup.closure (((insert γ S) : Finset G) : Set G) = ⊤)
    (Λ₀ : ℝ) (hΛ₀ : 0 < Λ₀) (ξ : Finset (MonoidAlgebra ℝ G))
    (hξ : OnPropertyT.Laplacian S ^ 2 - Λ₀ • OnPropertyT.Laplacian S = ∑ x ∈ ξ, star x * x) :
    PropertyT G := by
  classical
  set g : MonoidAlgebra ℝ G := MonoidAlgebra.of ℝ G γ with hg
  set e : MonoidAlgebra ℝ G := (2:ℝ)⁻¹ • (1 - g) with hedef
  set Λ : ℝ := min Λ₀ 1 with hΛdef
  have hΛpos : 0 < Λ := lt_min hΛ₀ (by norm_num)
  have hΛle : Λ ≤ Λ₀ := min_le_left _ _
  have hΛle1 : Λ ≤ 1 := min_le_right _ _
  have hg2 : g * g = 1 := by rw [hg]; exact of_mul_self_of_involution γ hγ
  have he2 : e * e = e := by rw [hedef, hg]; exact half_one_sub_idem γ hγ
  have hgcomm : g * OnPropertyT.Laplacian S = OnPropertyT.Laplacian S * g := by
    rw [hg]; exact of_comm_laplacian S γ hγ hΔγ
  have hcommg : (1 - g) * OnPropertyT.Laplacian S = OnPropertyT.Laplacian S * (1 - g) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hgcomm]
  have hcomm : e * OnPropertyT.Laplacian S = OnPropertyT.Laplacian S * e := by
    rw [hedef, smul_mul_assoc, mul_smul_comm, hcommg]
  have hstarg : star (1 - g) = 1 - g := by
    rw [hg, _root_.star_sub, _root_.star_one, Submission.Helpers.star_of,
      inv_eq_of_mul_eq_one_right hγ]
  have hgg : (1 - g) * (1 - g) = (2:ℝ) • (1 - g) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hg2]
    rw [two_smul ℝ (1 - g)]
    abel
  have hge : (2:ℝ) • e = 1 - g := by
    rw [hedef]
    exact smul_inv_smul₀ two_ne_zero (1 - g)
  -- the two-square expansion `(Δ_S + 2e)²`
  have hexp : (OnPropertyT.Laplacian S + (2:ℝ) • e) ^ 2
      = OnPropertyT.Laplacian S ^ 2 + (4:ℝ) • (OnPropertyT.Laplacian S * e) + (4:ℝ) • e := by
    rw [sq, add_mul, mul_add, mul_add, sq, mul_smul_comm, smul_mul_assoc, hcomm,
      smul_mul_smul, he2]
    module
  have hξ' : OnPropertyT.Laplacian S ^ 2
      = (∑ x ∈ ξ, star x * x) + Λ₀ • OnPropertyT.Laplacian S := sub_eq_iff_eq_add.mp hξ
  -- the main identity
  have hmain : OnPropertyT.Laplacian (insert γ S) ^ 2 - Λ • OnPropertyT.Laplacian (insert γ S)
      = (∑ x ∈ ξ, star x * x) + (Λ₀ - Λ) • OnPropertyT.Laplacian S
        + (4:ℝ) • (OnPropertyT.Laplacian S * e) + (4 - 2*Λ) • e := by
    rw [laplacian_insert_eq S γ hγS, hexp, hξ']
    simp only [smul_add]
    module
  -- the paper's form of the Laplacian, in `Fintype`-sum form over the subtype `S`
  have htwo : (2:ℝ) • OnPropertyT.Laplacian S
      = ∑ s : S, star (1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - MonoidAlgebra.of ℝ G (s : G)) := by
    rw [show (2:ℝ) • OnPropertyT.Laplacian S
          = (2 : MonoidAlgebra ℝ G) * OnPropertyT.Laplacian S by
        rw [Algebra.smul_def, map_ofNat]]
    rw [two_mul_laplacian_eq_sum_sq S hsym]
    exact (Finset.sum_coe_sort S (fun s =>
      star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s))).symm
  -- piece 1 : `(Λ₀ - Λ) • Δ_S` as a sum of hermitian squares
  have ha2 : Real.sqrt ((Λ₀ - Λ)/2) * Real.sqrt ((Λ₀ - Λ)/2) = (Λ₀ - Λ)/2 :=
    Real.mul_self_sqrt (by linarith)
  have hp1 : (Λ₀ - Λ) • OnPropertyT.Laplacian S
      = ∑ s : S, star (Real.sqrt ((Λ₀ - Λ)/2) • (1 - MonoidAlgebra.of ℝ G (s : G)))
          * (Real.sqrt ((Λ₀ - Λ)/2) • (1 - MonoidAlgebra.of ℝ G (s : G))) := by
    rw [show (Λ₀ - Λ) • OnPropertyT.Laplacian S
          = ((Λ₀ - Λ)/2) • ((2:ℝ) • OnPropertyT.Laplacian S) by
        rw [← smul_assoc]; congr 1; ring]
    rw [htwo, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun s _ => by
      rw [smul_star_mul_smul, ha2])
  -- piece 2 : `4 • (Δ_S * e)` as a sum of hermitian squares
  have hstep : ∀ z : MonoidAlgebra ℝ G, star (z * (1 - g)) * (z * (1 - g))
      = (1 - g) * (star z * z) * (1 - g) := by
    intro z
    rw [StarMul.star_mul, hstarg]
    noncomm_ring
  have hsum1 : (∑ s : S, (1 - g)
        * (star (1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - MonoidAlgebra.of ℝ G (s : G))) * (1 - g))
      = (1 - g) * (∑ s : S, star (1 - MonoidAlgebra.of ℝ G (s : G))
          * (1 - MonoidAlgebra.of ℝ G (s : G))) * (1 - g) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hsum2 : (∑ s : S, star ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g))
        * ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g)))
      = (8:ℝ) • (OnPropertyT.Laplacian S * e) := by
    rw [Finset.sum_congr rfl (fun s _ => hstep _), hsum1, ← htwo]
    rw [mul_smul_comm, smul_mul_assoc, hcommg, mul_assoc, hgg, mul_smul_comm, ← hge,
      mul_smul_comm]
    rw [← smul_assoc, ← smul_assoc]
    norm_num
  have hb2 : Real.sqrt ((2:ℝ)⁻¹) * Real.sqrt ((2:ℝ)⁻¹) = (2:ℝ)⁻¹ :=
    Real.mul_self_sqrt (by norm_num)
  have hp2 : (4:ℝ) • (OnPropertyT.Laplacian S * e)
      = ∑ s : S, star (Real.sqrt ((2:ℝ)⁻¹) • ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g)))
          * (Real.sqrt ((2:ℝ)⁻¹) • ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g))) := by
    have h4 : (4:ℝ) • (OnPropertyT.Laplacian S * e)
        = (2:ℝ)⁻¹ • (∑ s : S, star ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g))
            * ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g))) := by
      rw [hsum2, ← smul_assoc]
      module
    rw [h4, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun s _ =>
      Eq.trans (by rw [hb2]) (smul_star_mul_smul (Real.sqrt ((2:ℝ)⁻¹))
        ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g))).symm)
  -- piece 3 : `(4 - 2Λ) • e` as a sum of hermitian squares
  have hc2 : Real.sqrt ((4 - 2*Λ)/4) * Real.sqrt ((4 - 2*Λ)/4) = (4 - 2*Λ)/4 :=
    Real.mul_self_sqrt (by linarith)
  have hp3 : (4 - 2*Λ) • e
      = ∑ _ : Unit, star (Real.sqrt ((4 - 2*Λ)/4) • (1 - g))
          * (Real.sqrt ((4 - 2*Λ)/4) • (1 - g)) := by
    rw [Fintype.sum_unique, smul_star_mul_smul, hc2, hstarg, hgg, ← smul_assoc]
    module
  -- piece 4 : the given certificate
  have hp4 : (∑ x ∈ ξ, star x * x)
      = ∑ i : {x // x ∈ ξ}, star (i : MonoidAlgebra ℝ G) * (i : MonoidAlgebra ℝ G) :=
    (Finset.sum_coe_sort ξ (fun x => star x * x)).symm
  -- the four pieces as one index-type sum
  let Y1 : {x // x ∈ ξ} → MonoidAlgebra ℝ G := fun x => (x : MonoidAlgebra ℝ G)
  let Y2 : S → MonoidAlgebra ℝ G :=
    fun s => Real.sqrt ((Λ₀ - Λ)/2) • (1 - MonoidAlgebra.of ℝ G (s : G))
  let Y3 : S → MonoidAlgebra ℝ G :=
    fun s => Real.sqrt ((2:ℝ)⁻¹) • ((1 - MonoidAlgebra.of ℝ G (s : G)) * (1 - g))
  let Y4 : Unit → MonoidAlgebra ℝ G :=
    fun _ => Real.sqrt ((4 - 2*Λ)/4) • (1 - g)
  let Y : ({x // x ∈ ξ} ⊕ (S ⊕ (S ⊕ Unit))) → MonoidAlgebra ℝ G :=
    Sum.elim Y1 (Sum.elim Y2 (Sum.elim Y3 Y4))
  have hY : (∑ i, star (Y i) * (Y i))
      = (∑ x ∈ ξ, star x * x) + (Λ₀ - Λ) • OnPropertyT.Laplacian S
        + (4:ℝ) • (OnPropertyT.Laplacian S * e) + (4 - 2*Λ) • e := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Y, Y1, Y2, Y3, Y4, Sum.elim_inl, Sum.elim_inr]
    rw [← hp4, ← hp1, ← hp2, ← hp3]
    abel
  -- merge the index-type sum into a Finset sum
  obtain ⟨ζ, hζ⟩ := merge_sq_fintype Y
  have hfinal : OnPropertyT.Laplacian (insert γ S) ^ 2 - Λ • OnPropertyT.Laplacian (insert γ S)
      = ∑ z ∈ ζ, star z * z := by
    rw [hmain, ← hY, hζ]
  refine ⟨insert γ S, ?_, hgen, Λ, hΛpos, ζ, hfinal⟩
  -- symmetry of the generating set
  ext x
  rw [Set.mem_inv, Finset.mem_coe, Finset.mem_insert, Finset.mem_coe, Finset.mem_insert]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [← inv_inv x, h, inv_eq_of_mul_eq_one_right hγ])
    · exact Or.inr (Submission.PropertyT.mem_of_inv_mem hsym h)
  · rintro (h | h)
    · exact Or.inl (by rw [h, inv_eq_of_mul_eq_one_right hγ])
    · exact Or.inr (Submission.PropertyT.inv_mem_of_mem hsym h)

end

end Submission.RouteB
