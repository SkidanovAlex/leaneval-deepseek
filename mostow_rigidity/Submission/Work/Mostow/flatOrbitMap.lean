import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.flatActNearStab
import Submission.Work.Mostow.flatActFactorization
import Submission.Work.Mostow.flatCoverRadius

/-!
# The flat orbit map between two horospherical stabilisers

Let `Γ, Λ ≤ PO n 1`, `f : Γ ≃* Λ`, and `ξ, η ∈ Sph n` with `f(Γ_ξ) = Λ_η` (up to the level-one
condition on the base point), each stabiliser acting cocompactly on the level-one horosphere of its
boundary point.  On the flat spaces `ξ^⊥` and `η^⊥` the horospherical actions are flat actions, and
the orbit map of `f`

`ψ y = flatAct η (f (δ y)) y₀`,  where `δ y ∈ Γ_ξ` brings `y` into a fixed ball,

is a coarse equivalence: it is a quasi-isometry `ξ^⊥ → η^⊥` (both coarse Lipschitz bounds), it is
coarsely surjective, and it is coarsely equivariant for `f`, with a constant uniform in the group
element.  This is the "flat orbit map" used to build the cusp part of the equivariant
quasi-isometry `QIProp`.

The proof is the standard orbit-map argument.  For `δ y ≔ ρ y` chosen so that
`‖flatAct ξ (ρ y) 0 - y‖ ≤ R` we have `ψ y = flatAct η (f (ρ y)) 0`; the *new* observation for the
`δ`-clause is that for a level-one stabiliser element `g`
`‖flatAct ξ g⁻¹ y‖ = ‖y - flatAct ξ g 0‖` (`fo_flatAct_inv_apply_norm`), so the norm of the flat
action of `(δ y)⁻¹` on `y` is exactly the distance of `flatAct ξ (δ y) 0` from `y`.
-/

set_option maxHeartbeats 8000000
attribute [local irreducible] Work.Mostow.flatAct

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-! ## Elementary helpers -/

/-- Level preservation from level one at the origin. -/
theorem fo_lev_of_zero {ξ : E n} (hA : POBasic n) (hI : HypIsoData n) (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ) (h0 : lev ξ (g • (0 : E n)) = 1) :
    ∀ u : E n, lev ξ (g • u) = lev ξ u := by
  intro u
  rw [lev_smul_self hI hA ξ hξ g u hg, h0, mul_one]

theorem fo_lev_zero (ξ : E n) : lev ξ (0 : E n) = 1 := by
  simp [lev, tpart]

theorem fo_lev_smul_zero {ξ : E n} (hA : POBasic n) (hI : HypIsoData n) (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ) (h : ∀ u : E n, lev ξ (g • u) = lev ξ u) :
    lev ξ (g • (0 : E n)) = 1 := by
  rw [h (0 : E n)]; exact fo_lev_zero ξ

theorem fo_list_prod_coe {G : Subgroup (PO n 1)} (l : List G) :
    (l.map (fun g => (g : PO n 1))).prod = ((l.prod : G) : PO n 1) := by
  have h := map_list_prod (Subgroup.subtype G) l
  simpa using h

theorem fo_list_sum_map_const {α : Type*} (l : List α) (c : ℝ) :
    (l.map (fun _ => c)).sum = (l.length : ℝ) * c := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; rw [ih, Nat.cast_add, Nat.cast_one]; ring

theorem fo_smul_segment_sub (x y : E n) (a b : ℝ) :
    (x + a • (y - x)) - (x + b • (y - x)) = (a - b) • (y - x) := by
  rw [sub_smul]
  abel

/-- The coarse Lipschitz bound from a local (unit-scale) bound, inside a hyperplane. -/
theorem fo_norm_sub_le_mul_add {ξ : E n} {φ : E n → E n} {K : ℝ} (hK : 0 ≤ K)
    (hloc : ∀ x y : E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 → ‖x - y‖ ≤ 1 →
      ‖φ x - φ y‖ ≤ K) :
    ∀ x y : E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
      ‖φ x - φ y‖ ≤ K * ‖x - y‖ + K := by
  intro x y hx hy
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, norm_zero, mul_zero, zero_add]
    exact hK
  · have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
    set m : ℕ := max 1 (Nat.ceil ‖x - y‖) with hmdef
    have hm1 : 1 ≤ m := le_max_left _ _
    have hm2 : (m : ℝ) ≤ ‖x - y‖ + 1 := by
      rw [hmdef, Nat.cast_max]
      refine max_le ?_ ?_
      · push_cast; linarith [norm_nonneg (x - y)]
      · exact le_of_lt (Nat.ceil_lt_add_one (norm_nonneg _))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
    have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
    have hmge : ‖x - y‖ ≤ (m : ℝ) := by
      rw [hmdef, Nat.cast_max]
      exact le_trans (Nat.le_ceil ‖x - y‖) (le_max_right _ _)
    set z : ℕ → E n := fun i => x + ((i : ℝ) / (m : ℝ)) • (y - x) with hzdef
    have hzmem : ∀ i : ℕ, inner ℝ (z i) ξ = 0 := by
      intro i
      have h2 : inner ℝ (y - x) ξ = 0 := by rw [inner_sub_left, hy, hx, sub_zero]
      simp only [hzdef, inner_add_left, hx, real_inner_smul_left, h2, mul_zero, add_zero]
    have hstep : ∀ i < m, ‖z i - z (i + 1)‖ ≤ 1 := by
      intro i hi
      have hcoef : (i : ℝ) / (m : ℝ) - ((i : ℝ) + 1) / (m : ℝ) = -(1 / (m : ℝ)) := by
        field_simp
        ring
      have hsub : z i - z (i + 1) = ((i : ℝ) / (m : ℝ) - ((i : ℝ) + 1) / (m : ℝ)) • (y - x) := by
        have h1 : z i = x + ((i : ℝ) / (m : ℝ)) • (y - x) := rfl
        have h2 : z (i + 1) = x + (((i : ℝ) + 1) / (m : ℝ)) • (y - x) := by
          show x + (((i + 1 : ℕ) : ℝ) / (m : ℝ)) • (y - x)
              = x + (((i : ℝ) + 1) / (m : ℝ)) • (y - x)
          rw [Nat.cast_add, Nat.cast_one]
        rw [h1, h2, fo_smul_segment_sub]
      rw [hsub, hcoef, neg_smul, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)), one_div, inv_mul_le_iff₀ hmpos,
        mul_one, norm_sub_rev]
      exact hmge
    have hzf0 : z 0 = x := by simp [hzdef]
    have hzfm : z m = y := by
      simp only [hzdef]
      rw [div_self hmne, one_smul, add_sub_cancel]
    have key : ∀ j : ℕ, j ≤ m → ‖φ x - φ (z j)‖ ≤ (j : ℝ) * K := by
      intro j
      induction j with
      | zero => intro _; simp [hzf0]
      | succ j ih =>
        intro hj
        have hjm : j ≤ m := Nat.le_of_succ_le hj
        have hlt : j < m := Nat.lt_of_succ_le hj
        calc ‖φ x - φ (z (j + 1))‖
            ≤ ‖φ x - φ (z j)‖ + ‖φ (z j) - φ (z (j + 1))‖ := by
              rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
              exact dist_triangle _ _ _
          _ ≤ (j : ℝ) * K + K :=
              add_le_add (ih hjm)
                (hloc (z j) (z (j + 1)) (hzmem j) (hzmem (j + 1)) (hstep j hlt))
          _ = ((j + 1 : ℕ) : ℝ) * K := by push_cast; ring
    have hfin := key m le_rfl
    rw [hzfm] at hfin
    calc ‖φ x - φ y‖ ≤ (m : ℝ) * K := hfin
      _ ≤ (‖x - y‖ + 1) * K := mul_le_mul_of_nonneg_right hm2 hK
      _ = K * ‖x - y‖ + K := by ring

/-! ## Lists of elements of a subgroup -/

theorem fo_bd_list_prod_coe {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n)
    {Γ : Subgroup (PO n 1)} {l : List Γ} (h : ∀ g ∈ l, bd (((g : Γ)) : PO n 1) ξ = ξ) :
    bd ((((l.prod : Γ)) : PO n 1)) ξ = ξ := by
  induction l with
  | nil => rw [List.prod_nil, Subgroup.coe_one]; exact hA.bd_one ξ hξ
  | cons g t ih =>
    rw [List.prod_cons, Subgroup.coe_mul]
    exact bd_mul_of hξ hA (h g (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem fo_lev_list_prod_coe {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)} {l : List Γ}
    (h : ∀ g ∈ l, bd (((g : Γ)) : PO n 1) ξ = ξ ∧
      lev ξ ((((g : Γ)) : PO n 1) • (0 : E n)) = 1) :
    lev ξ ((((l.prod : Γ)) : PO n 1) • (0 : E n)) = 1 := by
  induction l with
  | nil => rw [List.prod_nil, Subgroup.coe_one, hA.one_smul]; exact fo_lev_zero ξ
  | cons g t ih =>
    have hg : bd (((g : Γ)) : PO n 1) ξ = ξ := (h g (by simp)).1
    have hg0 : lev ξ ((((g : Γ)) : PO n 1) • (0 : E n)) = 1 := (h g (by simp)).2
    have ht0 : lev ξ ((((t.prod : Γ)) : PO n 1) • (0 : E n)) = 1 :=
      ih (fun x hx => h x (by simp [hx]))
    rw [List.prod_cons, Subgroup.coe_mul, hA.mul_smul,
      lev_smul_self hI hA ξ hξ (((g : Γ)) : PO n 1) ((((t.prod : Γ)) : PO n 1) • (0 : E n)) hg,
      hg0, ht0]
    simp

theorem fo_flatAct_prod_norm_le' {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)} {l : List Γ}
    (hbd : ∀ g ∈ l, bd (((g : Γ)) : PO n 1) ξ = ξ)
    (h0 : ∀ g ∈ l, lev ξ ((((g : Γ)) : PO n 1) • (0 : E n)) = 1) :
    ‖flatAct ξ ((((l.prod : Γ)) : PO n 1)) (0 : E n)‖ ≤
      (l.map (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum := by
  induction l with
  | nil =>
    rw [List.prod_nil, List.map_nil, List.sum_nil, Subgroup.coe_one,
      flatAct_one hξ hA (by simp : inner ℝ (0 : E n) ξ = 0)]
    exact norm_zero.le
  | cons g t ih =>
    have hgt : bd (((g : Γ)) : PO n 1) ξ = ξ := hbd g (by simp)
    have h0g : lev ξ ((((g : Γ)) : PO n 1) • (0 : E n)) = 1 := h0 g (by simp)
    have hbt : bd ((((t.prod : Γ)) : PO n 1)) ξ = ξ :=
      fo_bd_list_prod_coe hξ hA (fun x hx => hbd x (by simp [hx]))
    have h0t : lev ξ ((((t.prod : Γ)) : PO n 1) • (0 : E n)) = 1 :=
      fo_lev_list_prod_coe hξ hA hI (fun x hx => ⟨hbd x (by simp [hx]), h0 x (by simp [hx])⟩)
    rw [List.prod_cons, List.map_cons, List.sum_cons, Subgroup.coe_mul]
    have hcomp : flatAct ξ ((((g : Γ)) : PO n 1) * (((t.prod : Γ)) : PO n 1)) (0 : E n)
        = flatAct ξ (((g : Γ)) : PO n 1) (flatAct ξ ((((t.prod : Γ)) : PO n 1)) (0 : E n)) :=
      flatAct_comp hξ hA hI hgt hbt h0g h0t (by simp : inner ℝ (0 : E n) ξ = 0)
    rw [hcomp]
    calc ‖flatAct ξ (((g : Γ)) : PO n 1) (flatAct ξ ((((t.prod : Γ)) : PO n 1)) (0 : E n))‖
        ≤ ‖flatAct ξ (((g : Γ)) : PO n 1) (flatAct ξ ((((t.prod : Γ)) : PO n 1)) (0 : E n))
            - flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖
          + ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖ := by
          have h := norm_add_le
            (flatAct ξ (((g : Γ)) : PO n 1) (flatAct ξ ((((t.prod : Γ)) : PO n 1)) (0 : E n))
              - flatAct ξ (((g : Γ)) : PO n 1) (0 : E n))
            (flatAct ξ (((g : Γ)) : PO n 1) (0 : E n))
          rwa [sub_add_cancel] at h
      _ = ‖flatAct ξ ((((t.prod : Γ)) : PO n 1)) (0 : E n)‖
          + ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖ := by
          rw [flatAct_isometry (y := flatAct ξ ((((t.prod : Γ)) : PO n 1)) (0 : E n))
            (y' := (0 : E n)) hξ hA hI hgt h0g (flatAct_mem hξ _ (0 : E n))
            (by simp : inner ℝ (0 : E n) ξ = 0), sub_zero]
      _ ≤ (t.map (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum
          + ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖ := by
          linarith [ih (fun x hx => hbd x (by simp [hx])) (fun x hx => h0 x (by simp [hx]))]
      _ = ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖
          + (t.map (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum := by ring

/-! ## The displacement comparison -/

theorem fo_flatDispComp {n : ℕ} (hA : POBasic n) (hI : HypIsoData n)
    {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ)
    {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hstab : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      bd (((f γ : Λ)) : PO n 1) η = η)
    (hstab' : ∀ m : Λ, bd (((m : Λ)) : PO n 1) η = η →
      ∃ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ ∧ f γ = m)
    (hlevξ : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ ((((γ : Γ)) : PO n 1) • u) = lev ξ u)
    (hlevη : ∀ m : Λ, bd (((m : Λ)) : PO n 1) η = η →
      ∀ u : E n, lev η ((((m : Λ)) : PO n 1) • u) = lev η u)
    (hdiscΛ : IsDiscrete (SetLike.coe Λ))
    {R₁ : ℝ} (hR₁ : 0 < R₁)
    (hcovη : ∀ x : E n, inner ℝ x η = 0 → ∃ m : Λ,
      bd (((m : Λ)) : PO n 1) η = η ∧
      ‖flatAct η (((m : Λ)) : PO n 1) (0 : E n) - x‖ ≤ R₁) :
    ∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧ ∀ (γ : Γ)
      (hγ : bd (((γ : Γ)) : PO n 1) ξ = ξ),
      ‖flatAct ξ (((γ : Γ)) : PO n 1) (0 : E n)‖ ≤
        L * ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ + C := by
  classical
  -- level one at the origin for the η-stabiliser
  have h0η : ∀ m : Λ, bd (((m : Λ)) : PO n 1) η = η →
      lev η ((((m : Λ)) : PO n 1) • (0 : E n)) = 1 :=
    fun m hm => fo_lev_smul_zero hA hI hη _ hm (hlevη m hm)
  -- membership of `f⁻¹ m` in the ξ-stabiliser
  have hmemξ : ∀ m : Λ, bd (((m : Λ)) : PO n 1) η = η →
      bd (((f.symm m : Γ)) : PO n 1) ξ = ξ := by
    intro m hm
    obtain ⟨γ, hγ, hfγ⟩ := hstab' m hm
    have hs : f.symm m = γ := f.injective (by rw [MulEquiv.apply_symm_apply]; exact hfγ.symm)
    rw [hs]; exact hγ
  -- finiteness of the η-near-stabiliser
  have hfin : {m : Λ | bd (((m : Λ)) : PO n 1) η = η ∧
      ‖flatAct η (((m : Λ)) : PO n 1) (0 : E n)‖ ≤ 3 * R₁}.Finite :=
    flatActNearStab hA hI hη hdiscΛ h0η (3 * R₁)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ m : Λ, bd (((m : Λ)) : PO n 1) η = η →
      ‖flatAct η (((m : Λ)) : PO n 1) (0 : E n)‖ ≤ 3 * R₁ →
      ‖flatAct ξ (((f.symm m : Γ)) : PO n 1) (0 : E n)‖ ≤ K := by
    obtain ⟨K, hK⟩ := (hfin.image
      (fun m => ‖flatAct ξ (((f.symm m : Γ)) : PO n 1) (0 : E n)‖)).bddAbove
    exact ⟨K, fun m hm hmn => hK ⟨m, ⟨hm, hmn⟩, rfl⟩⟩
  refine ⟨max (max K 0 / R₁) 1, max (3 * max K 0) 0, le_max_right _ _, le_max_right _ _, ?_⟩
  intro γ hγ
  obtain ⟨l, hlen, hmem, hprod⟩ :=
    flatActFactorization (Γ := Λ) (ξ := η) hA hI hη hlevη hR₁ hcovη (f γ) (hstab γ hγ)
  -- `γ` as the product of the `f`-preimages of the factors of `f γ`
  have hγprod : γ = (l.map (fun m => f.symm m)).prod := by
    have h1 : (l.map (fun m => f.symm m)).prod = γ := by
      have h := map_list_prod (f.symm) l
      rw [hprod] at h
      simpa using h.symm
    exact h1.symm
  have hnorm : ‖flatAct ξ (((γ : Γ)) : PO n 1) (0 : E n)‖
      ≤ ((l.map (fun m => f.symm m)).map
          (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum := by
    rw [hγprod]
    exact fo_flatAct_prod_norm_le' hξ hA hI
      (fun g hg => by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
        exact hmemξ m (hmem m hm).1)
      (fun g hg => by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
        exact fo_lev_smul_zero hA hI hξ _ (hmemξ m (hmem m hm).1)
          (hlevξ _ (hmemξ m (hmem m hm).1)))
  have hsum_le : ((l.map (fun m => f.symm m)).map
      (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum
      ≤ (l.length : ℝ) * max K 0 := by
    have h1 : ∀ g ∈ (l.map (fun m => f.symm m)),
        ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖ ≤ max K 0 := by
      intro g hg
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
      exact le_trans (hK m (hmem m hm).1 (hmem m hm).2) (le_max_left _ _)
    calc ((l.map (fun m => f.symm m)).map
          (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum
        ≤ ((l.map (fun m => f.symm m)).map (fun _ => max K 0)).sum := List.sum_le_sum h1
      _ = (l.length : ℝ) * max K 0 := by
          rw [fo_list_sum_map_const, List.length_map]
  have hlen_l : (l.length : ℝ) ≤
      ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ / R₁ + 3 := by
    have h1 : (l.length : ℝ) ≤
        (Nat.ceil (‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ / R₁) : ℝ) + 2 := by
      exact_mod_cast hlen
    have h2 : (Nat.ceil (‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ / R₁) : ℝ)
        < ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ / R₁ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  have hDnn : (0 : ℝ) ≤ ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ := norm_nonneg _
  calc ‖flatAct ξ (((γ : Γ)) : PO n 1) (0 : E n)‖
      ≤ ((l.map (fun m => f.symm m)).map
          (fun g => ‖flatAct ξ (((g : Γ)) : PO n 1) (0 : E n)‖)).sum := hnorm
    _ ≤ (l.length : ℝ) * max K 0 := hsum_le
    _ ≤ (‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ / R₁ + 3) * max K 0 :=
        mul_le_mul_of_nonneg_right hlen_l (le_max_right _ _)
    _ = (max K 0 / R₁) * ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ + 3 * max K 0 := by
        ring
    _ ≤ (max (max K 0 / R₁) 1) * ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖
        + max (3 * max K 0) 0 := by
        have h3 : (max K 0 / R₁) * ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖
            ≤ (max (max K 0 / R₁) 1) * ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hDnn
        have h4 : 3 * max K 0 ≤ max (3 * max K 0) 0 := le_max_left _ _
        linarith


/-- The composition law for `flatAct` in terms of subgroup elements. -/
theorem fo_flatAct_coe_mul {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)}
    (hlev : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ ((((γ : Γ)) : PO n 1) • u) = lev ξ u)
    {a b : Γ} (ha : bd (((a : Γ)) : PO n 1) ξ = ξ) (hb : bd (((b : Γ)) : PO n 1) ξ = ξ)
    {y : E n} (hy : inner ℝ y ξ = 0) :
    flatAct ξ (((a * b : Γ)) : PO n 1) y
      = flatAct ξ (((a : Γ)) : PO n 1) (flatAct ξ (((b : Γ)) : PO n 1) y) := by
  rw [Subgroup.coe_mul]
  exact flatAct_comp hξ hA hI ha hb
    (fo_lev_smul_zero hA hI hξ _ ha (hlev a ha)) (fo_lev_smul_zero hA hI hξ _ hb (hlev b hb)) hy

/-- The isometry law for `flatAct` in terms of subgroup elements. -/
theorem fo_flatAct_coe_isometry {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {Γ : Subgroup (PO n 1)}
    (hlev : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ ((((γ : Γ)) : PO n 1) • u) = lev ξ u)
    {a : Γ} (ha : bd (((a : Γ)) : PO n 1) ξ = ξ)
    {y y' : E n} (hy : inner ℝ y ξ = 0) (hy' : inner ℝ y' ξ = 0) :
    ‖flatAct ξ (((a : Γ)) : PO n 1) y - flatAct ξ (((a : Γ)) : PO n 1) y'‖ = ‖y - y'‖ :=
  flatAct_isometry (g := (((a : Γ)) : PO n 1)) hξ hA hI ha
    (fo_lev_smul_zero hA hI hξ (((a : Γ)) : PO n 1) ha (hlev a ha)) hy hy'

/-- Auxiliary: `‖flatAct ξ (↑a) 0 - flatAct ξ (↑b) 0‖ = ‖flatAct ξ (↑(b⁻¹a)) 0‖`
for `a b` in the `ξ`-stabiliser. -/
theorem fo_norm_flatAct_sub_eq {ξ : E n} (hA : POBasic n) (hI : HypIsoData n) (hξ : ξ ∈ Sph n)
    {Γ : Subgroup (PO n 1)}
    (hlev : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ ((((γ : Γ)) : PO n 1) • u) = lev ξ u)
    {a b : Γ} (ha : bd (((a : Γ)) : PO n 1) ξ = ξ) (hb : bd (((b : Γ)) : PO n 1) ξ = ξ) :
    ‖flatAct ξ (((a : Γ)) : PO n 1) (0 : E n) - flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)‖
      = ‖flatAct ξ ((((b⁻¹ * a : Γ))) : PO n 1) (0 : E n)‖ := by
  have hbi : bd (((b⁻¹ : Γ)) : PO n 1) ξ = ξ := bd_inv_of hξ hA hb
  have hcomp1 : flatAct ξ (((b⁻¹ : Γ)) : PO n 1) (flatAct ξ (((a : Γ)) : PO n 1) (0 : E n))
      = flatAct ξ ((((b⁻¹ * a : Γ))) : PO n 1) (0 : E n) :=
    (fo_flatAct_coe_mul hξ hA hI hlev hbi ha (by simp : inner ℝ (0 : E n) ξ = 0)).symm
  have hcomp2 : flatAct ξ (((b⁻¹ : Γ)) : PO n 1) (flatAct ξ (((b : Γ)) : PO n 1) (0 : E n))
      = (0 : E n) := by
    rw [← fo_flatAct_coe_mul hξ hA hI hlev hbi hb (by simp : inner ℝ (0 : E n) ξ = 0),
      inv_mul_cancel b, Subgroup.coe_one, flatAct_one hξ hA (by simp : inner ℝ (0 : E n) ξ = 0)]
  have hiso := fo_flatAct_coe_isometry (y := flatAct ξ (((a : Γ)) : PO n 1) (0 : E n))
    (y' := flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)) hξ hA hI hlev hbi
    (flatAct_mem hξ (((a : Γ)) : PO n 1) (0 : E n))
    (flatAct_mem hξ (((b : Γ)) : PO n 1) (0 : E n))
  rw [hcomp1, hcomp2, sub_zero] at hiso
  exact hiso.symm

/-- The address bound: if `flatAct ξ (↑a) 0` is `R`-close to `x` and `flatAct ξ (↑b) 0` is
`R`-close to `y`, then `‖flatAct ξ (↑(b⁻¹ a)) 0‖ ≤ 2R + ‖y - x‖`. -/
theorem fo_frame_addr_le {ξ : E n} (hA : POBasic n) (hI : HypIsoData n) (hξ : ξ ∈ Sph n)
    {Γ : Subgroup (PO n 1)}
    (hlev : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ ((((γ : Γ)) : PO n 1) • u) = lev ξ u)
    {a b : Γ} (ha : bd (((a : Γ)) : PO n 1) ξ = ξ) (hb : bd (((b : Γ)) : PO n 1) ξ = ξ)
    {x y : E n} {R : ℝ}
    (hax : ‖flatAct ξ (((a : Γ)) : PO n 1) (0 : E n) - x‖ ≤ R)
    (hby : ‖flatAct ξ (((b : Γ)) : PO n 1) (0 : E n) - y‖ ≤ R) :
    ‖flatAct ξ ((((b⁻¹ * a : Γ))) : PO n 1) (0 : E n)‖ ≤ 2 * R + ‖y - x‖ := by
  rw [← fo_norm_flatAct_sub_eq hA hI hξ hlev ha hb]
  have h1 : ‖flatAct ξ (((a : Γ)) : PO n 1) (0 : E n) - flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)‖
      ≤ ‖flatAct ξ (((a : Γ)) : PO n 1) (0 : E n) - x‖ + ‖x - y‖
        + ‖y - flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)‖ := by
    calc ‖flatAct ξ (((a : Γ)) : PO n 1) (0 : E n) - flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)‖
        = dist (flatAct ξ (((a : Γ)) : PO n 1) (0 : E n))
            (flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)) := (dist_eq_norm _ _).symm
      _ ≤ dist (flatAct ξ (((a : Γ)) : PO n 1) (0 : E n)) x + dist x y
            + dist y (flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)) := by
          have h2 := dist_triangle (flatAct ξ (((a : Γ)) : PO n 1) (0 : E n)) x y
          have h3 := dist_triangle (flatAct ξ (((a : Γ)) : PO n 1) (0 : E n)) y
            (flatAct ξ (((b : Γ)) : PO n 1) (0 : E n))
          linarith
      _ = ‖flatAct ξ (((a : Γ)) : PO n 1) (0 : E n) - x‖ + ‖x - y‖
            + ‖y - flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)‖ := by
          rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have h2 : ‖y - flatAct ξ (((b : Γ)) : PO n 1) (0 : E n)‖ ≤ R := by
    rw [norm_sub_rev]; exact hby
  have h3 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
  linarith

/-! ## The inverse-translation identity for the flat action -/

/-- If `g` preserves the level function `lev ξ ·`, so does its inverse, at the base point. -/
theorem fo_lev_inv_zero {ξ : E n} (hA : POBasic n) {g : PO n 1}
    (hlevg : ∀ u : E n, lev ξ (g • u) = lev ξ u) : lev ξ (g⁻¹ • (0 : E n)) = 1 := by
  rw [← hlevg (g⁻¹ • (0 : E n)), ← hA.mul_smul, mul_inv_cancel, hA.one_smul]
  exact fo_lev_zero ξ

/-- For a level-one element `g` of the `ξ`-stabiliser and `y ∈ ξ^⊥`, the flat action of `g⁻¹` on
`y` has norm the Euclidean distance from `y` to the flat displacement of `g`. -/
theorem fo_flatAct_inv_apply_norm {ξ : E n} (hA : POBasic n) (hI : HypIsoData n)
    (hξ : ξ ∈ Sph n) {g : PO n 1} (hg : bd g ξ = ξ) (h0 : lev ξ (g • (0 : E n)) = 1)
    (hlevg : ∀ u : E n, lev ξ (g • u) = lev ξ u) {y : E n} (hy : inner ℝ y ξ = 0) :
    ‖flatAct ξ g⁻¹ y‖ = ‖y - flatAct ξ g (0 : E n)‖ := by
  have hgi : bd g⁻¹ ξ = ξ := bd_inv_of hξ hA hg
  have h0i : lev ξ (g⁻¹ • (0 : E n)) = 1 := fo_lev_inv_zero hA hlevg
  have hz : inner ℝ (0 : E n) ξ = 0 := by simp
  have hcomp : flatAct ξ g⁻¹ (flatAct ξ g (0 : E n)) = 0 := by
    have h := flatAct_comp hξ hA hI hgi hg h0i h0 hz
    rw [inv_mul_cancel, flatAct_one hξ hA hz] at h
    exact h.symm
  have hiso := flatAct_isometry (g := g⁻¹) hξ hA hI hgi h0i
    (y := y) (y' := flatAct ξ g (0 : E n)) hy (flatAct_mem hξ g (0 : E n))
  rw [hcomp, sub_zero] at hiso
  exact hiso


theorem flatOrbitMap (n : ℕ) (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} (f : Γ ≃* Λ)
    (hdiscΓ : IsDiscrete (SetLike.coe Γ)) (hdiscΛ : IsDiscrete (SetLike.coe Λ))
    {ξ η : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hη : η ∈ Submission.Mostow.Sph n)
    (hstab : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Submission.Mostow.bd ((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η)
    (hstab' : ∀ m : Λ, Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      ∃ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧ f γ = m)
    (hlevξ : ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 1)
    (hlevη : ∀ m : Λ, Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η →
      Work.Mostow.lev η (((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • (0 : Submission.Mostow.E n)) = 1)
    (hcpt : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K)
    (hcptη : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ v : Submission.Mostow.E n,
      Work.Mostow.lev η v = 1 → ∃ m : Λ, Submission.Mostow.bd ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) η = η ∧
        ((m : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1) • v ∈ K) :
    ∃ (ψ : Submission.Mostow.E n → Submission.Mostow.E n) (δ : Submission.Mostow.E n → Γ)
      (y₀ : Submission.Mostow.E n) (R : ℝ),
      inner ℝ y₀ η = 0 ∧ 0 ≤ R ∧
      (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 →
        Submission.Mostow.bd (((δ y)⁻¹ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        Work.Mostow.lev ξ ((((δ y)⁻¹ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) •
          (0 : Submission.Mostow.E n)) = 1 ∧
        ‖Work.Mostow.flatAct ξ (((δ y)⁻¹ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) y‖ ≤ R ∧
        inner ℝ (ψ y) η = 0 ∧
        ψ y = Work.Mostow.flatAct η (((f (δ y) : Λ)) : LeanEval.Geometry.MostowRigidity.PO n 1) y₀) ∧
      (∃ L C : ℝ, 1 ≤ L ∧ 0 ≤ C ∧
        (∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
          ‖ψ x - ψ y‖ ≤ L * ‖x - y‖ + C) ∧
        (∀ x y : Submission.Mostow.E n, inner ℝ x ξ = 0 → inner ℝ y ξ = 0 →
          ‖x - y‖ ≤ L * ‖ψ x - ψ y‖ + C)) ∧
      (∃ C : ℝ, ∀ z : Submission.Mostow.E n, inner ℝ z η = 0 →
        ∃ x : Submission.Mostow.E n, inner ℝ x ξ = 0 ∧ ‖ψ x - z‖ ≤ C) ∧
      (∃ C : ℝ, ∀ γ : Γ, Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
        ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 →
        ‖ψ (Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)) x)
          - Work.Mostow.flatAct η (((f γ : Λ) : LeanEval.Geometry.MostowRigidity.PO n 1)) (ψ x)‖ ≤ C) := by

  classical
  -- Level preservation for the two horospherical stabilisers
  have hlvξ : ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ∀ u : E n, lev ξ ((((γ : Γ)) : PO n 1) • u) = lev ξ u :=
    fun γ hγ => fo_lev_of_zero hA hI hξ _ hγ (hlevξ γ hγ)
  have hlvη : ∀ m : Λ, bd (((m : Λ)) : PO n 1) η = η →
      ∀ u : E n, lev η ((((m : Λ)) : PO n 1) • u) = lev η u :=
    fun m hm => fo_lev_of_zero hA hI hη _ hm (hlevη m hm)
  -- Covering radii for the flat actions
  obtain ⟨R, hRpos, hcov⟩ := flatCoverRadius hA hI hξ hlvξ hcpt
  obtain ⟨R₁, hR₁pos, hcovη⟩ := flatCoverRadius hA hI hη hlvη hcptη
  have hRnn : (0 : ℝ) ≤ R := le_of_lt hRpos
  -- Comparison of the flat displacements on the two sides
  obtain ⟨L, C, hL, hC, hcmp⟩ :=
    fo_flatDispComp hA hI f hξ hη hstab hstab' hlvξ hlvη hdiscΛ hR₁pos hcovη
  -- A uniform bound for the `η`-displacement of a `ξ`-near-stabilising element
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, ∀ γ : Γ, bd (((γ : Γ)) : PO n 1) ξ = ξ →
      ‖flatAct ξ (((γ : Γ)) : PO n 1) (0 : E n)‖ ≤ 2 * R + 1 →
      ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖ ≤ K₂ := by
    have hfinS : {γ : Γ | bd (((γ : Γ)) : PO n 1) ξ = ξ ∧
        ‖flatAct ξ (((γ : Γ)) : PO n 1) (0 : E n)‖ ≤ 2 * R + 1}.Finite :=
      flatActNearStab hA hI hξ hdiscΓ hlevξ (2 * R + 1)
    obtain ⟨K₂, hK₂⟩ := (hfinS.image
      (fun γ => ‖flatAct η (((f γ : Λ)) : PO n 1) (0 : E n)‖)).bddAbove
    exact ⟨K₂, fun γ hγ hb => hK₂ ⟨γ, ⟨hγ, hb⟩, rfl⟩⟩
  -- The correcting elements `δ y`: they bring the flat point `y` back into the ball of radius `R`
  have hcovall : ∀ y : E n, ∃ γ : Γ,
      (inner ℝ y ξ = 0 → bd (((γ : Γ)) : PO n 1) ξ = ξ ∧
        ‖flatAct ξ (((γ : Γ)) : PO n 1) (0 : E n) - y‖ ≤ R) := by
    intro y
    by_cases hy : inner ℝ y ξ = 0
    · obtain ⟨γ, h1, h2⟩ := hcov y hy
      exact ⟨γ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hy⟩
  let ρ : E n → Γ := fun y => (hcovall y).choose
  have hρ : ∀ y : E n, ∀ hy : inner ℝ y ξ = 0,
      bd (((ρ y : Γ)) : PO n 1) ξ = ξ ∧
        ‖flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n) - y‖ ≤ R :=
    fun y hy => (hcovall y).choose_spec hy
  let ψ : E n → E n := fun x => flatAct η (((f (ρ x) : Λ)) : PO n 1) (0 : E n)
  have hψ : ∀ x : E n, ψ x = flatAct η (((f (ρ x) : Λ)) : PO n 1) (0 : E n) := fun x => rfl
  let sg : E n → E n → Γ := fun x y => (ρ x)⁻¹ * ρ y
  have hsg : ∀ x y : E n, ρ x * sg x y = ρ y := by
    intro x y
    simp only [sg]
    group
  have hkey : ∀ x y : E n, ∀ hx : inner ℝ x ξ = 0, ∀ hy : inner ℝ y ξ = 0,
      ‖ψ x - ψ y‖ = ‖flatAct η ((((f (sg x y) : Λ))) : PO n 1) (0 : E n)‖ := by
    intro x y hx hy
    have hsbd : bd ((((sg x y : Γ))) : PO n 1) ξ = ξ :=
      bd_mul_of hξ hA (bd_inv_of hξ hA (hρ x hx).1) (hρ y hy).1
    have hcomp : flatAct η (((f (ρ x) : Λ)) : PO n 1)
        (flatAct η (((f (sg x y) : Λ)) : PO n 1) (0 : E n))
        = flatAct η (((f (ρ y) : Λ)) : PO n 1) (0 : E n) := by
      rw [← fo_flatAct_coe_mul (Γ := Λ) hη hA hI hlvη (hstab (ρ x) (hρ x hx).1)
        (hstab (sg x y) hsbd) (by simp : inner ℝ (0 : E n) η = 0), ← map_mul, hsg x y]
    have hiso := fo_flatAct_coe_isometry (Γ := Λ) hη hA hI hlvη (hstab (ρ x) (hρ x hx).1)
      (y := flatAct η (((f (sg x y) : Λ)) : PO n 1) (0 : E n)) (y' := (0 : E n))
      (flatAct_mem hη _ (0 : E n)) (by simp : inner ℝ (0 : E n) η = 0)
    rw [hcomp, sub_zero] at hiso
    rw [hψ, hψ, ← hiso, norm_sub_rev]
  have hsn : ∀ x y : E n, ∀ hx : inner ℝ x ξ = 0, ∀ hy : inner ℝ y ξ = 0,
      ‖flatAct ξ (((sg x y : Γ)) : PO n 1) (0 : E n)‖ ≤ 2 * R + ‖x - y‖ := by
    intro x y hx hy
    exact fo_frame_addr_le hA hI hξ hlvξ (hρ y hy).1 (hρ x hx).1 (hρ y hy).2 (hρ x hx).2
  refine ⟨ψ, ρ, 0, R, by simp, hRnn, ?_,
    ⟨max (max (max K₂ 0) L) 1, max (max (max K₂ 0) (2 * R + C)) 0, ?_, ?_, ?_, ?_⟩,
    ⟨max K₂ 0 + R₁, ?_⟩, ?_⟩
  · -- the properties of the correcting elements `δ y = ρ y`
    intro y hy
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.coe_inv]
      exact bd_inv_of hξ hA (hρ y hy).1
    · rw [Subgroup.coe_inv]
      exact fo_lev_inv_zero hA (hlvξ (ρ y) (hρ y hy).1)
    · rw [Subgroup.coe_inv,
        fo_flatAct_inv_apply_norm hA hI hξ (hρ y hy).1 (hlevξ (ρ y) (hρ y hy).1)
          (hlvξ (ρ y) (hρ y hy).1) hy, norm_sub_rev]
      exact (hρ y hy).2
    · show inner ℝ (flatAct η (((f (ρ y) : Λ)) : PO n 1) (0 : E n)) η = 0
      exact flatAct_mem hη _ _
    · exact hψ y
  · exact le_max_right _ _
  · exact le_max_right _ _
  · -- `ψ` is coarsely Lipschitz
    intro x y hx hy
    have hbdρ : ∀ (a b : E n), inner ℝ a ξ = 0 → inner ℝ b ξ = 0 →
        bd ((((sg a b : Γ))) : PO n 1) ξ = ξ := fun a b ha hb =>
      bd_mul_of hξ hA (bd_inv_of hξ hA (hρ a ha).1) (hρ b hb).1
    have hloc : ∀ a b : E n, inner ℝ a ξ = 0 → inner ℝ b ξ = 0 → ‖a - b‖ ≤ 1 →
        ‖ψ a - ψ b‖ ≤ max K₂ 0 := by
      intro a b ha hb hab
      rw [hkey a b ha hb]
      exact le_trans (hK₂ _ (hbdρ a b ha hb) (by linarith [hsn a b ha hb])) (le_max_left _ _)
    have hbound := fo_norm_sub_le_mul_add (le_max_right K₂ 0) hloc x y hx hy
    calc ‖ψ x - ψ y‖ ≤ max K₂ 0 * ‖x - y‖ + max K₂ 0 := hbound
      _ ≤ max (max (max K₂ 0) L) 1 * ‖x - y‖ + max (max (max K₂ 0) (2 * R + C)) 0 := by
          have h1 : max K₂ 0 ≤ max (max (max K₂ 0) L) 1 :=
            le_trans (le_max_left (max K₂ 0) L) (le_max_left _ _)
          have h2 : max K₂ 0 ≤ max (max (max K₂ 0) (2 * R + C)) 0 :=
            le_trans (le_max_left (max K₂ 0) (2 * R + C)) (le_max_left _ _)
          have hn : (0 : ℝ) ≤ ‖x - y‖ := norm_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right h1 hn]
  · -- `ψ` is coarsely expansive
    intro x y hx hy
    have hbdρ : bd ((((sg x y : Γ))) : PO n 1) ξ = ξ :=
      bd_mul_of hξ hA (bd_inv_of hξ hA (hρ x hx).1) (hρ y hy).1
    have hcmp' := hcmp _ hbdρ
    have htri : ‖x - y‖ ≤ 2 * R + ‖flatAct ξ ((((sg x y : Γ))) : PO n 1) (0 : E n)‖ := by
      have h1 : ‖x - flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)‖ ≤ R := by
        rw [norm_sub_rev]; exact (hρ x hx).2
      have h2 : ‖flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n) - y‖ ≤ R := (hρ y hy).2
      have h3 : ‖flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)
          - flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n)‖
            = ‖flatAct ξ ((((sg x y : Γ))) : PO n 1) (0 : E n)‖ := by
        rw [norm_sub_rev]
        exact fo_norm_flatAct_sub_eq hA hI hξ hlvξ (hρ y hy).1 (hρ x hx).1
      have h4 : ‖x - y‖ ≤ ‖x - flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)‖
          + ‖flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)
            - flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n)‖
          + ‖flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n) - y‖ := by
        calc ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
          _ ≤ dist x (flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n))
                + dist (flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n))
                  (flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n))
                + dist (flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n)) y := by
              have h5 := dist_triangle x (flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n))
                (flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n))
              have h6 := dist_triangle x (flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n)) y
              linarith
          _ = ‖x - flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)‖
                + ‖flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)
                  - flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n)‖
                + ‖flatAct ξ (((ρ y : Γ)) : PO n 1) (0 : E n) - y‖ := by
              rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      rw [h3] at h4
      linarith
    calc ‖x - y‖ ≤ 2 * R + ‖flatAct ξ ((((sg x y : Γ))) : PO n 1) (0 : E n)‖ := htri
      _ ≤ 2 * R + (L * ‖flatAct η ((((f (sg x y) : Λ))) : PO n 1) (0 : E n)‖ + C) := by
          linarith
      _ = L * ‖ψ x - ψ y‖ + (2 * R + C) := by rw [hkey x y hx hy]; ring
      _ ≤ max (max (max K₂ 0) L) 1 * ‖ψ x - ψ y‖ + max (max (max K₂ 0) (2 * R + C)) 0 := by
          have h1 : L ≤ max (max (max K₂ 0) L) 1 :=
            le_trans (le_max_right (max K₂ 0) L) (le_max_left _ _)
          have h2 : 2 * R + C ≤ max (max (max K₂ 0) (2 * R + C)) 0 :=
            le_trans (le_max_right (max K₂ 0) (2 * R + C)) (le_max_left _ _)
          have hn : (0 : ℝ) ≤ ‖ψ x - ψ y‖ := norm_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right h1 hn]
  · -- coarse surjectivity
    intro z hz
    obtain ⟨m, hm, hmz⟩ := hcovη z hz
    obtain ⟨γ₀, hγ₀, hfγ₀⟩ := hstab' m hm
    set x : E n := flatAct ξ (((γ₀ : Γ)) : PO n 1) (0 : E n) with hxdef
    have hxmem : inner ℝ x ξ = 0 := flatAct_mem hξ _ (0 : E n)
    refine ⟨x, hxmem, ?_⟩
    set s : Γ := γ₀⁻¹ * ρ x with hsdef
    have hsbd : bd ((s : Γ) : PO n 1) ξ = ξ := by
      rw [hsdef]
      exact bd_mul_of hξ hA (bd_inv_of hξ hA hγ₀) (hρ x hxmem).1
    have hsnorm : ‖flatAct ξ ((s : Γ) : PO n 1) (0 : E n)‖ ≤ R := by
      rw [hsdef, ← fo_norm_flatAct_sub_eq hA hI hξ hlvξ (hρ x hxmem).1 hγ₀, ← hxdef]
      exact (hρ x hxmem).2
    have hK2s : ‖flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)‖ ≤ max K₂ 0 :=
      le_trans (hK₂ _ (by rw [hsdef]; exact bd_mul_of hξ hA (bd_inv_of hξ hA hγ₀) (hρ x hxmem).1)
        (by linarith [hsnorm, hRnn])) (le_max_left _ _)
    have hψx : ψ x = flatAct η (((f γ₀ : Λ)) : PO n 1)
        (flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)) := by
      have hρxs : ρ x = (γ₀ : Γ) * s := by rw [hsdef]; group
      rw [hψ, hρxs, map_mul, fo_flatAct_coe_mul (Γ := Λ) hη hA hI hlvη (hstab γ₀ hγ₀)
        (hstab s (by rw [hsdef]; exact bd_mul_of hξ hA (bd_inv_of hξ hA hγ₀) (hρ x hxmem).1))
        (by simp : inner ℝ (0 : E n) η = 0)]
    have hiso := fo_flatAct_coe_isometry (Γ := Λ) hη hA hI hlvη (hstab γ₀ hγ₀)
      (y := flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)) (y' := (0 : E n))
      (flatAct_mem hη _ (0 : E n)) (by simp : inner ℝ (0 : E n) η = 0)
    rw [← hψx] at hiso
    rw [sub_zero] at hiso
    calc ‖ψ x - z‖
        ≤ ‖ψ x - flatAct η (((f γ₀ : Λ)) : PO n 1) (0 : E n)‖
          + ‖flatAct η (((f γ₀ : Λ)) : PO n 1) (0 : E n) - z‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
          exact dist_triangle _ _ _
      _ = ‖flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)‖
          + ‖flatAct η (((f γ₀ : Λ)) : PO n 1) (0 : E n) - z‖ := by rw [hiso]
      _ ≤ max K₂ 0 + R₁ := by
          rw [← hfγ₀] at hmz
          linarith
  · -- coarse equivariance, with a constant uniform in `γ`
    refine ⟨max K₂ 0, fun γ hγ x hx => ?_⟩
    set x' : E n := flatAct ξ (((γ : Γ)) : PO n 1) x with hx'def
    have hx'mem : inner ℝ x' ξ = 0 := flatAct_mem hξ _ _
    set s : Γ := (((γ : Γ)) * ρ x)⁻¹ * ρ x' with hsdef
    have hsbd : bd ((s : Γ) : PO n 1) ξ = ξ := by
      rw [hsdef]
      exact bd_mul_of hξ hA (bd_inv_of hξ hA (bd_mul_of hξ hA hγ (hρ x hx).1)) (hρ x' hx'mem).1
    have hsnorm : ‖flatAct ξ ((s : Γ) : PO n 1) (0 : E n)‖ ≤ 2 * R := by
      rw [hsdef, ← fo_norm_flatAct_sub_eq hA hI hξ hlvξ (hρ x' hx'mem).1
        (bd_mul_of hξ hA hγ (hρ x hx).1)]
      have h2 : ‖flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n) - x'‖ ≤ R := by
        have hA1 : flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n)
            = flatAct ξ ((((γ : Γ)) : PO n 1)) (flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)) :=
          fo_flatAct_coe_mul hξ hA hI hlvξ hγ (hρ x hx).1 (by simp : inner ℝ (0 : E n) ξ = 0)
        rw [hA1, hx'def]
        rw [fo_flatAct_coe_isometry (y := flatAct ξ (((ρ x : Γ)) : PO n 1) (0 : E n)) (y' := x)
          hξ hA hI hlvξ hγ (flatAct_mem hξ (((ρ x : Γ)) : PO n 1) (0 : E n)) hx]
        exact (hρ x hx).2
      have h1 : ‖flatAct ξ (((ρ x' : Γ)) : PO n 1) (0 : E n) - x'‖ ≤ R := (hρ x' hx'mem).2
      calc ‖flatAct ξ (((ρ x' : Γ)) : PO n 1) (0 : E n)
            - flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n)‖
          = dist (flatAct ξ (((ρ x' : Γ)) : PO n 1) (0 : E n))
              (flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n)) := (dist_eq_norm _ _).symm
        _ ≤ dist (flatAct ξ (((ρ x' : Γ)) : PO n 1) (0 : E n)) x'
              + dist x' (flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n)) :=
            dist_triangle _ _ _
        _ = ‖flatAct ξ (((ρ x' : Γ)) : PO n 1) (0 : E n) - x'‖
              + ‖x' - flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n)‖ := by
            rw [dist_eq_norm, dist_eq_norm] <;> ring
        _ ≤ 2 * R := by
            have h2' : ‖x' - flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n)‖
                = ‖flatAct ξ ((((γ : Γ)) * ρ x : Γ) : PO n 1) (0 : E n) - x'‖ :=
              norm_sub_rev _ _
            linarith
    have hK2s : ‖flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)‖ ≤ max K₂ 0 :=
      le_trans (hK₂ _ hsbd (by linarith [hsnorm])) (le_max_left _ _)
    have hx's : ρ x' = ((γ : Γ)) * ρ x * s := by
      rw [hsdef]
      group
    have h1 : ψ x' = flatAct η (((f ((((γ : Γ)) * ρ x) : Γ) : Λ)) : PO n 1)
        (flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)) := by
      rw [hψ, hx's, map_mul]
      rw [fo_flatAct_coe_mul (Γ := Λ) hη hA hI hlvη
        (hstab (((γ : Γ)) * ρ x) (bd_mul_of hξ hA hγ (hρ x hx).1))
        (hstab s hsbd) (by simp : inner ℝ (0 : E n) η = 0)]
    have h2 : flatAct η (((f γ : Λ)) : PO n 1) (ψ x)
        = flatAct η (((f ((((γ : Γ)) * ρ x) : Γ) : Λ)) : PO n 1) (0 : E n) := by
      rw [hψ]
      rw [← fo_flatAct_coe_mul (Γ := Λ) hη hA hI hlvη (hstab γ hγ) (hstab (ρ x) (hρ x hx).1)
        (by simp : inner ℝ (0 : E n) η = 0)]
      congr 1
      rw [map_mul]
    have hiso := fo_flatAct_coe_isometry (Γ := Λ) hη hA hI hlvη
      (hstab (((γ : Γ)) * ρ x) (bd_mul_of hξ hA hγ (hρ x hx).1))
      (y := flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)) (y' := (0 : E n))
      (flatAct_mem hη _ (0 : E n)) (by simp : inner ℝ (0 : E n) η = 0)
    calc ‖ψ x' - flatAct η (((f γ : Λ)) : PO n 1) (ψ x)‖
        = ‖flatAct η (((f ((((γ : Γ)) * ρ x) : Γ) : Λ)) : PO n 1)
            (flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n))
          - flatAct η (((f ((((γ : Γ)) * ρ x) : Γ) : Λ)) : PO n 1) (0 : E n)‖ := by rw [h1, h2]
      _ = ‖flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n) - 0‖ := hiso
      _ = ‖flatAct η (((f ((s : Γ)) : Λ)) : PO n 1) (0 : E n)‖ := by rw [sub_zero]
      _ ≤ max K₂ 0 := hK2s


end Work.Mostow
