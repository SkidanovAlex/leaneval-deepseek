import Mathlib
import Submission.Mostow.GeodDefs
import Submission.Work.Mostow.bieberbachDefs
import Submission.Work.Mostow.dirichletBox
import Submission.Work.Mostow.orthSmallCommute
import Submission.Work.Mostow.abelianBlockStructure

/-!
# G4 of the strata chapter: a cardinality bound for finite subgroups of `O(m)`

`Work.Mostow.cardKernelTorus`: for every `m` there is `J > 0` such that every finite subgroup
`A ≤ O(m)` whose non-identity elements are `v`-separated from `1` in operator norm
(`Submission.Mostow.rotN`) satisfies `|A| ≤ J * (1 + v ^ (-⌊m/2⌋))`.

Proof.  `Work.Mostow.exists_abelian_subgroup_index` finds an abelian subgroup `B ≤ A` with
`|A| ≤ J₀ * |B|`: the "small" elements of `A` (those with `mOf ≤ c₀`) pairwise commute
(`Work.Mostow.orthSmallCommute`, the Frobenius/Engel argument) and generate `B`, which therefore
has index bounded by the size `J₀` of a fixed `c₀/2`-cover of `O(m)` (`Work.Mostow.exists_cover_rotations`).
`Work.Mostow.abelianCardBound` bounds `|B|` from `Work.Mostow.abelianBlockStructure` (simultaneous
block structure of a finite abelian subgroup: `r` rotation blocks and `s` sign characters with
`2r + s ≤ m`), the box counting `Work.Mostow.card_le_of_torusData` on the torus `(ℝ/2πℤ)^r`, and the
arithmetic `Work.Mostow.abelian_arith`.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

/-- **Counting a finite subgroup of the torus with a coordinatewise separation.**

If every nonzero element of a finite subgroup `Λ ≤ (ℝ/2πℤ)^r` has a coordinate of norm `≥ v`,
then `|Λ| ≤ (1 + 2π/v)^r`.  (Pigeonhole over the `⌈2π/v⌉` boxes of each coordinate: two
elements in the same box differ by an element all of whose coordinates have norm `< v`.) -/
theorem torusCard_le {r : ℕ} (Λ : AddSubgroup (Fin r → AddCircle (2 * Real.pi))) [Finite Λ]
    {v : ℝ} (hv : 0 < v) (hsep : ∀ a ∈ Λ, a ≠ 0 → ∃ i, v ≤ ‖a i‖) :
    (Nat.card Λ : ℝ) ≤ (1 + 2 * Real.pi / v) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    haveI : Fintype Λ := Fintype.ofFinite Λ
    haveI hsub : Subsingleton (Fin 0 → AddCircle (2 * Real.pi)) :=
      ⟨fun f g => funext fun i => i.elim0⟩
    have h1 : Fintype.card Λ ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr
        ⟨fun x y => Subtype.ext (Subsingleton.elim (x : Fin 0 → AddCircle (2 * Real.pi)) y)⟩
    have h2 : (Nat.card Λ : ℝ) ≤ 1 := by
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast h1
    simpa using h2
  · have hvπ : 0 < 2 * Real.pi / v := by positivity
    have hα : ∀ _ : Fin r, 0 < v := fun _ => hv
    haveI : Fintype Λ := Fintype.ofFinite Λ
    let f : Λ → ((i : Fin r) → Fin ⌈2 * Real.pi / v⌉₊) :=
      fun a i => boxIdx (fun _ : Fin r => v) hα i (a.1 i)
    have hf : Function.Injective f := by
      intro a b hab
      have hcoord : ∀ i, ‖(a.1 : Fin r → AddCircle (2 * Real.pi)) i - b.1 i‖ < v := by
        intro i
        have h := boxIdx_eq_imp (fun _ : Fin r => v) hα i (congrFun hab i)
        simpa [f] using h
      have hmem : (a.1 - b.1) ∈ Λ := Λ.sub_mem a.2 b.2
      have hzero : a.1 - b.1 = 0 := by
        by_contra hne
        obtain ⟨i, hi⟩ := hsep (a.1 - b.1) hmem hne
        have h2 : ‖(a.1 - b.1) i‖ < v := by simpa [Pi.sub_apply] using hcoord i
        linarith
      exact Subtype.ext (sub_eq_zero.mp hzero)
    have hcard : Nat.card Λ ≤ Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / v⌉₊) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective f hf
    have hprod : Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / v⌉₊)
        = ⌈2 * Real.pi / v⌉₊ ^ r := by
      rw [Fintype.card_pi]
      simp [Finset.prod_const]
    have hceil : ((⌈2 * Real.pi / v⌉₊ : ℕ) : ℝ) ≤ 1 + 2 * Real.pi / v := by
      have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * Real.pi / v by positivity)
      push_cast
      linarith
    calc (Nat.card Λ : ℝ) ≤ (Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / v⌉₊) : ℝ) := by
          exact_mod_cast hcard
      _ = ((⌈2 * Real.pi / v⌉₊ : ℕ) : ℝ) ^ r := by rw [hprod]; push_cast; ring
      _ ≤ (1 + 2 * Real.pi / v) ^ r := by
          exact pow_le_pow_left₀ (by positivity) hceil r


/-- **Cardinality bound from torus data.**

If a finite subgroup `A ≤ O(m)` is `v`-separated from the identity and carries "torus data"
`ψ : A → (ℝ/2πℤ)^r`, `σ : A → (ℤ/2)^s`, additive and jointly injective, with
`rotN a ≤ ∑ i, ‖ψ a i‖ + (2 if σ a ≠ 0)`, then `|A| ≤ 2^s * (1 + 2π r / v)^r`: split `A` by the
sign map, and on its kernel count the rotation angles by box counting on the torus. -/
theorem card_le_of_torusData {m : ℕ} (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite A]
    {v : ℝ} (hv : 0 < v) (hsep : ∀ a ∈ A, a ≠ 1 → v ≤ rotN a)
    {r s : ℕ} (hrs : 2 * r + s ≤ m)
    (ψ : A → (Fin r → AddCircle (2 * Real.pi))) (σ : A → (Fin s → ZMod 2))
    (hψ1 : ψ 1 = 0) (hσ1 : σ 1 = 0)
    (hψadd : ∀ a b : A, ψ (a * b) = ψ a + ψ b)
    (hσadd : ∀ a b : A, σ (a * b) = σ a + σ b)
    (hinj : ∀ a : A, ψ a = 0 → σ a = 0 → a = 1)
    (hnorm : ∀ a : A, σ a = 0 → rotN (a : E m ≃ₗᵢ[ℝ] E m) ≤ ∑ i : Fin r, ‖ψ a i‖) :
    (Nat.card A : ℝ) ≤ 2 ^ s * (1 + 2 * Real.pi * r / v) ^ r := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  -- the sign map as a homomorphism
  let σh : A →* Multiplicative (Fin s → ZMod 2) :=
    { toFun := fun a => Multiplicative.ofAdd (σ a)
      map_one' := by rw [hσ1]; rfl
      map_mul' := by
        intro a b
        show Multiplicative.ofAdd (σ (a * b)) = Multiplicative.ofAdd (σ a) * Multiplicative.ofAdd (σ b)
        rw [hσadd]
        rfl }
  have hσh : ∀ a : A, σh a = Multiplicative.ofAdd (σ a) := fun a => rfl
  have hmemker : ∀ a : A, a ∈ σh.ker ↔ σ a = 0 := by
    intro a
    rw [MonoidHom.mem_ker, hσh]
    exact ⟨fun h => Multiplicative.ofAdd.injective h, fun h => by rw [h]; rfl⟩
  -- `|A| = |ker| * |range|` and the range has at most `2^s` elements
  have hcardA : Nat.card A = Nat.card σh.ker * Nat.card σh.range := by
    have h1 : Nat.card σh.ker * σh.ker.index = Nat.card A := Subgroup.card_mul_index σh.ker
    rw [Subgroup.index_ker] at h1
    omega
  have hrange : (Nat.card σh.range : ℝ) ≤ 2 ^ s := by
    have h1 : Nat.card σh.range ≤ Nat.card (Multiplicative (Fin s → ZMod 2)) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective (Subtype.val) Subtype.val_injective
    have h2 : Nat.card (Multiplicative (Fin s → ZMod 2)) = 2 ^ s := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_pi]
      simp [ZMod.card]
    have h3 : (Nat.card σh.range : ℝ) ≤ (2 : ℝ) ^ s := by
      rw [h2] at h1
      exact_mod_cast h1
    simpa using h3
  -- the kernel is bounded by box counting
  have hkernel : (Nat.card σh.ker : ℝ) ≤ (1 + 2 * Real.pi * r / v) ^ r := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have h1 : Nat.card σh.ker ≤ 1 := by
        rw [Nat.card_eq_fintype_card]
        refine Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
        have ha : (a : A) = 1 := hinj (a : A) (Subsingleton.elim _ _) ((hmemker _).mp a.2)
        have hb : (b : A) = 1 := hinj (b : A) (Subsingleton.elim _ _) ((hmemker _).mp b.2)
        exact Subtype.ext (ha.trans hb.symm)
      have h2 : (Nat.card σh.ker : ℝ) ≤ 1 := by exact_mod_cast h1
      simpa using h2
    · have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
      have hα : ∀ _ : Fin r, 0 < v / r := fun _ => div_pos hv hrpos
      have hboxes : Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / (v / r)⌉₊)
          = ⌈2 * Real.pi / (v / r)⌉₊ ^ r := by
        rw [Fintype.card_pi]
        simp [Finset.prod_const]
      have hψinv : ∀ a : A, ψ a⁻¹ = - ψ a := by
        intro a
        have h := hψadd a⁻¹ a
        rw [inv_mul_cancel, hψ1] at h
        exact eq_neg_of_add_eq_zero_left h.symm
      have hψsub : ∀ a b : A, ψ (a⁻¹ * b) = ψ b - ψ a := by
        intro a b
        rw [hψadd, hψinv, neg_add_eq_sub]
      have hσinv : ∀ a : A, σ a⁻¹ = - σ a := by
        intro a
        have h := hσadd a⁻¹ a
        rw [inv_mul_cancel, hσ1] at h
        exact eq_neg_of_add_eq_zero_left h.symm
      let f : σh.ker → ((i : Fin r) → Fin ⌈2 * Real.pi / (v / r)⌉₊) :=
        fun a i => boxIdx (fun _ : Fin r => v / r) hα i (ψ (a : A) i)
      have hf : Function.Injective f := by
        intro a b hab
        have hbox : ∀ i, boxIdx (fun _ : Fin r => v / r) hα i (ψ (a : A) i)
            = boxIdx (fun _ : Fin r => v / r) hα i (ψ (b : A) i) := by
          intro i
          simpa [f] using congrFun hab i
        have hcoord : ∀ i, ‖ψ (a : A) i - ψ (b : A) i‖ < v / r := by
          intro i
          exact boxIdx_eq_imp (fun _ : Fin r => v / r) hα i (hbox i)
        have hker : (a : A)⁻¹ * (b : A) ∈ σh.ker := by
          rw [hmemker, hσadd, hσinv, (hmemker _).mp a.2, (hmemker _).mp b.2]
          simp
        have hψval : ∀ i, ‖ψ ((a : A)⁻¹ * (b : A)) i‖ < v / r := by
          intro i
          rw [hψsub]
          simpa [Pi.sub_apply, norm_sub_rev] using hcoord i
        have hone : (a : A)⁻¹ * (b : A) = 1 := by
          set c : A := (a : A)⁻¹ * (b : A) with hc
          have hck : σ c = 0 := by
            rw [hc, hσadd, hσinv, (hmemker _).mp a.2, (hmemker _).mp b.2]
            simp
          have hψc : ∀ i, ‖ψ c i‖ < v / r := by
            intro i
            have h := hψsub (a : A) (b : A)
            rw [← hc] at h
            rw [h]
            simpa [Pi.sub_apply, norm_sub_rev] using hcoord i
          by_contra hne
          have h1 : v ≤ rotN (c : E m ≃ₗᵢ[ℝ] E m) :=
            hsep _ c.2 (fun h => hne (Subtype.ext (by rw [hc] at h; exact h)))
          have h2 := hnorm c hck
          have hsum : (∑ i : Fin r, ‖ψ c i‖) < v := by
            have hle : ∀ i ∈ (Finset.univ : Finset (Fin r)), ‖ψ c i‖ ≤ v / r :=
              fun i _ => le_of_lt (hψc i)
            have hlt : ∃ i ∈ (Finset.univ : Finset (Fin r)), ‖ψ c i‖ < v / r :=
              ⟨⟨0, hr⟩, Finset.mem_univ _, hψc ⟨0, hr⟩⟩
            have h := Finset.sum_lt_sum hle hlt
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
            have h4 : (r : ℝ) * (v / r) = v := by
              field_simp
            linarith [h, h4]
          linarith [h1, h2, hsum]
        have hcoe2 : (a : A) = (b : A) := by
          calc (a : A) = (a : A) * ((a : A)⁻¹ * (b : A)) := by rw [hone, mul_one]
            _ = (b : A) := by group
        exact Subtype.ext hcoe2
      have hcard : Nat.card σh.ker ≤ Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / (v / r)⌉₊) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective f hf
      have hceil : ((⌈2 * Real.pi / (v / r)⌉₊ : ℕ) : ℝ) ≤ 1 + 2 * Real.pi * r / v := by
        have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * Real.pi / (v / r) by positivity)
        have h4 : 2 * Real.pi / (v / r) = 2 * Real.pi * r / v := by field_simp
        push_cast
        rw [h4] at h
        linarith
      calc (Nat.card σh.ker : ℝ)
          ≤ (Fintype.card ((i : Fin r) → Fin ⌈2 * Real.pi / (v / r)⌉₊) : ℝ) := by
            exact_mod_cast hcard
        _ = ((⌈2 * Real.pi / (v / r)⌉₊ : ℕ) : ℝ) ^ r := by rw [hboxes]; push_cast; ring
        _ ≤ (1 + 2 * Real.pi * r / v) ^ r := pow_le_pow_left₀ (by positivity) hceil r
  calc (Nat.card A : ℝ) = (Nat.card σh.ker : ℝ) * (Nat.card σh.range : ℝ) := by
        rw [hcardA]
        push_cast
        ring
    _ ≤ (1 + 2 * Real.pi * r / v) ^ r * 2 ^ s :=
        mul_le_mul hkernel hrange (by positivity) (by positivity)
    _ = 2 ^ s * (1 + 2 * Real.pi * r / v) ^ r := by ring


/-! ## From `Circle`-valued characters to torus data -/

/-- For `z` on the unit circle, `z = exp (arg z * I)`. -/
lemma circle_eq_exp_arg (z : Circle) :
    (z : ℂ) = Complex.exp ((Complex.arg (z : ℂ)) * Complex.I) := by
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [Circle.norm_coe] at h
  simpa using h.symm

/-- A point of the unit circle with vanishing argument is `1`. -/
lemma circle_eq_one_of_arg_eq_zero (z : Circle) (h : Complex.arg (z : ℂ) = 0) : z = 1 := by
  have h1 : (z : ℂ) = 1 := by
    rw [circle_eq_exp_arg z, h]
    simp
  exact Subtype.ext h1

/-- The norm of the angle of a point of the unit circle is its absolute argument. -/
lemma norm_arg_coe (z : Circle) :
    ‖((Complex.arg (z : ℂ) : ℝ) : AddCircle (2 * Real.pi))‖ = |Complex.arg (z : ℂ)| :=
  (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).mpr (by
    have h := Complex.arg_mem_Ioc (z : ℂ)
    rw [abs_le, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
    constructor <;> linarith [h.1, h.2])

/-- Chordal distance to `1` is at most the arc distance. -/
lemma norm_sub_one_le_norm_arg (z : Circle) :
    ‖(z : ℂ) - 1‖
      ≤ ‖((Complex.arg (z : ℂ) : ℝ) : AddCircle (2 * Real.pi))‖ := by
  have h1 : ‖(z : ℂ) - 1‖ = 2 * |Real.sin (Complex.arg (z : ℂ) / 2)| := by
    conv_lhs => rw [circle_eq_exp_arg z]
    rw [Complex.exp_ofReal_mul_I]
    rw [show ((Real.cos (Complex.arg (z : ℂ)) : ℂ)
          + (Real.sin (Complex.arg (z : ℂ)) : ℂ) * Complex.I) - 1
        = ((Real.cos (Complex.arg (z : ℂ)) - 1 : ℝ) : ℂ)
          + (Real.sin (Complex.arg (z : ℂ)) : ℂ) * Complex.I from by push_cast; ring,
      Complex.norm_add_mul_I]
    have hsq : Real.sin (Complex.arg (z : ℂ) / 2) ^ 2
        = 1 / 2 - Real.cos (Complex.arg (z : ℂ)) / 2 := by
      have h := Real.sin_sq_eq_half_sub (Complex.arg (z : ℂ) / 2)
      rw [show 2 * (Complex.arg (z : ℂ) / 2) = Complex.arg (z : ℂ) from by ring] at h
      exact h
    have h2 : (Real.cos (Complex.arg (z : ℂ)) - 1) ^ 2
        + Real.sin (Complex.arg (z : ℂ)) ^ 2
        = (2 * |Real.sin (Complex.arg (z : ℂ) / 2)|) ^ 2 := by
      rw [mul_pow, sq_abs, hsq, Real.sin_sq]
      ring
    rw [h2, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1, norm_arg_coe]
  have h3 : |Real.sin (Complex.arg (z : ℂ) / 2)| ≤ |Complex.arg (z : ℂ) / 2| :=
    Real.abs_sin_le_abs
  have h4 : 2 * |Complex.arg (z : ℂ) / 2| = |Complex.arg (z : ℂ)| := by
    rw [abs_div]
    ring
  linarith

/-- Additivity of the argument, transported to the additive circle of period `2π`. -/
lemma arg_coe_mul_add (u v : Circle) :
    ((Complex.arg (((u * v : Circle)) : ℂ) : ℝ) : AddCircle (2 * Real.pi))
      = ((Complex.arg (u : ℂ) : ℝ) : AddCircle (2 * Real.pi))
        + ((Complex.arg (v : ℂ) : ℝ) : AddCircle (2 * Real.pi)) := by
  have h := Complex.arg_mul_coe_angle (x := (u : ℂ)) (y := (v : ℂ))
    (by simpa using Circle.coe_ne_zero u) (by simpa using Circle.coe_ne_zero v)
  have hcoe : (((u * v : Circle)) : ℂ) = (u : ℂ) * (v : ℂ) := Circle.coe_mul u v
  rw [hcoe]
  exact h

/-- The `(ℤ/2)`-indicator of a product is the sum of the indicators, in `ℤ/2`. -/
lemma zmod2_indicator_mul (x y : Multiplicative (ZMod 2)) :
    (if x * y = 1 then (0 : ZMod 2) else 1)
      = (if x = 1 then 0 else 1) + (if y = 1 then 0 else 1) := by
  decide +revert

/-- If `x, y` are linear isometries of `E m` then `mOf (x⁻¹ * y) ≤ ‖opOf x - opOf y‖`. -/
lemma mOf_inv_mul_le {m : ℕ} (x y : E m ≃ₗᵢ[ℝ] E m) : mOf (x⁻¹ * y) ≤ ‖opOf x - opOf y‖ := by
  have hprod : opOf x⁻¹ * opOf x = 1 := opOf_inv_mul x
  have hfac : opOf (x⁻¹ * y) - 1 = opOf x⁻¹ * (opOf y - opOf x) := by
    rw [opOf_mul, mul_sub, hprod]
  rw [mOf, hfac]
  calc ‖opOf x⁻¹ * (opOf y - opOf x)‖ ≤ ‖opOf x⁻¹‖ * ‖opOf y - opOf x‖ := norm_mul_le _ _
    _ ≤ 1 * ‖opOf y - opOf x‖ := by
        gcongr
        exact norm_opOf_le_one x⁻¹
    _ = ‖opOf y - opOf x‖ := one_mul _
    _ = ‖opOf x - opOf y‖ := norm_sub_rev _ _

/-- **An abelian subgroup of bounded index.**  Every finite subgroup `A ≤ O(m)` contains an
abelian subgroup `B` with `|A| ≤ J₀ |B|`.

`B` is generated by the elements of `A` within `c₀` of the identity, where `c₀ > 0` is the
Frobenius constant of `Work.Mostow.orthSmallCommute`: those elements pairwise commute, so `B` is
abelian.  Covering `O(m)` by `J₀` balls of radius `c₀/2`, two elements of `A` in the same ball
differ by an element of `B`, so the natural map `A ⧸ B → (balls)` is injective and
`[A : B] ≤ J₀`. -/
theorem exists_abelian_subgroup_index (m : ℕ) :
    ∃ J₀ : ℝ, 0 < J₀ ∧ ∀ (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite A],
      ∃ B : Subgroup A, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
        (Nat.card A : ℝ) ≤ J₀ * (Nat.card B) := by
  obtain ⟨c₀, hc₀pos, hc₀⟩ := orthSmallCommute m
  obtain ⟨F, hF⟩ := exists_cover_rotations (m := m) (c₀ / 2) (by positivity)
  have hFne : 0 < F.card := by
    obtain ⟨f, hf, -⟩ := hF (1 : E m ≃ₗᵢ[ℝ] E m)
    exact F.card_pos.mpr ⟨f, hf⟩
  refine ⟨(F.card : ℝ), by exact_mod_cast hFne, ?_⟩
  intro A hAfin
  haveI : Fintype A := Fintype.ofFinite A
  set S : Set A := {a | mOf (a : E m ≃ₗᵢ[ℝ] E m) ≤ c₀} with hS
  set B : Subgroup A := Subgroup.closure S with hB
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hc₀ A x y hx hy)
  refine ⟨B, ?_, ?_⟩
  · intro x hx y hy
    -- every element of the closure commutes with every element of `S`
    have hgen : ∀ s ∈ S, ∀ y ∈ B, s * y = y * s := by
      intro s hs y hy
      rw [hB] at hy
      refine Subgroup.closure_induction (p := fun y _ => s * y = y * s) ?_ ?_ ?_ ?_ hy
      · intro t ht
        exact hcommS s hs t ht
      · rw [mul_one, one_mul]
      · intro y z hy hz hyy hzz
        calc s * (y * z) = (s * y) * z := by group
          _ = (y * s) * z := by rw [hyy]
          _ = y * (s * z) := by group
          _ = y * (z * s) := by rw [hzz]
          _ = y * z * s := by group
      · intro y hy hyy
        have hs : s = y⁻¹ * s * y := by
          calc s = y⁻¹ * (y * s) := by group
            _ = y⁻¹ * (s * y) := by rw [hyy]
            _ = y⁻¹ * s * y := by group
        conv_lhs => rw [hs]
        group
    have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      intro x hx
      rw [hB] at hx
      refine Subgroup.closure_induction (p := fun x _ => ∀ y ∈ B, x * y = y * x) ?_ ?_ ?_ ?_ hx
      · intro s hs y hy
        exact hgen s hs y hy
      · intro y hy
        rw [one_mul, mul_one]
      · intro x1 x2 hx1 hx2 hx1' hx2' y hy
        rw [mul_assoc, hx2' y hy, ← mul_assoc, hx1' y hy, mul_assoc]
      · intro x1 hx1 hx1' y hy
        calc x1⁻¹ * y = x1⁻¹ * (y * x1) * x1⁻¹ := by group
          _ = x1⁻¹ * (x1 * y) * x1⁻¹ := by rw [← hx1' y hy]
          _ = y * x1⁻¹ := by group
    exact hcommB x hx y hy
  · -- two elements of `A` in the same ball differ by an element of `B`
    have hsam : ∀ x y : A,
        ‖opOf ((x : A) : E m ≃ₗᵢ[ℝ] E m) - opOf ((y : A) : E m ≃ₗᵢ[ℝ] E m)‖ < c₀ →
        x⁻¹ * y ∈ B := by
      intro x y hxy
      have hsmall : mOf (((x⁻¹ * y) : A) : E m ≃ₗᵢ[ℝ] E m) < c₀ := by
        have h2 : mOf ((((x : A)) : E m ≃ₗᵢ[ℝ] E m)⁻¹ * ((y : A) : E m ≃ₗᵢ[ℝ] E m)) < c₀ :=
          lt_of_le_of_lt (mOf_inv_mul_le ((x : A) : E m ≃ₗᵢ[ℝ] E m)
            ((y : A) : E m ≃ₗᵢ[ℝ] E m)) hxy
        simpa using h2
      exact Subgroup.subset_closure (le_of_lt hsmall)
    -- the ball map on the cosets
    have hgg : ∀ q : A ⧸ B,
        ∃ f ∈ F, ‖opOf (((Quotient.out q) : A) : E m ≃ₗᵢ[ℝ] E m) - f‖ < c₀ / 2 :=
      fun q => hF _
    let g : A ⧸ B → ↥F :=
      fun q => ⟨Classical.choose (hgg q), (Classical.choose_spec (hgg q)).1⟩
    have hgval : ∀ q : A ⧸ B,
        ‖opOf (((Quotient.out q) : A) : E m ≃ₗᵢ[ℝ] E m) - (g q : E m →L[ℝ] E m)‖ < c₀ / 2 :=
      fun q => (Classical.choose_spec (hgg q)).2
    have hinj : Function.Injective g := by
      intro q q' hqq'
      have hval : (g q : E m →L[ℝ] E m) = (g q' : E m →L[ℝ] E m) := by rw [hqq']
      have hclose : ‖opOf (((Quotient.out q) : A) : E m ≃ₗᵢ[ℝ] E m)
          - opOf (((Quotient.out q') : A) : E m ≃ₗᵢ[ℝ] E m)‖ < c₀ := by
        have h1 := hgval q
        have h2 : ‖(g q : E m →L[ℝ] E m)
            - opOf (((Quotient.out q') : A) : E m ≃ₗᵢ[ℝ] E m)‖ < c₀ / 2 := by
          rw [hval, norm_sub_rev]
          exact hgval q'
        have h3 := dist_triangle (opOf (((Quotient.out q) : A) : E m ≃ₗᵢ[ℝ] E m))
          (g q : E m →L[ℝ] E m) (opOf (((Quotient.out q') : A) : E m ≃ₗᵢ[ℝ] E m))
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h3
        linarith
      have hmem : ((Quotient.out q)⁻¹ * (Quotient.out q') : A) ∈ B := hsam _ _ hclose
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact QuotientGroup.eq.mpr hmem
    have hindex : B.index ≤ F.card := by
      rw [Subgroup.index_eq_card]
      calc Nat.card (A ⧸ B) ≤ Nat.card ↥F := Nat.card_le_card_of_injective g hinj
        _ = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    calc (Nat.card A : ℝ) = (Nat.card B : ℝ) * (B.index : ℝ) := by
          rw [← Subgroup.card_mul_index B]
          push_cast
          ring
      _ ≤ (Nat.card B : ℝ) * (F.card : ℝ) := by
          have h : (B.index : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hindex
          exact mul_le_mul_of_nonneg_left h (by positivity)
      _ = (F.card : ℝ) * (Nat.card B) := by ring

/-- `(1 + 1/v)^k ≤ 2^k * (1 + (1/v)^k)` for `v > 0`. -/
lemma pow_one_add_inv_le (v : ℝ) (hv : 0 < v) (k : ℕ) :
    (1 + 1 / v) ^ k ≤ 2 ^ k * (1 + (1 / v) ^ k) := by
  have hv' : (0 : ℝ) < 1 / v := by positivity
  rcases le_or_gt 1 (1 / v) with h | h
  · have h1 : 1 + 1 / v ≤ 2 * (1 / v) := by linarith
    calc (1 + 1 / v) ^ k ≤ (2 * (1 / v)) ^ k := pow_le_pow_left₀ (by linarith) h1 k
      _ = 2 ^ k * (1 / v) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * (1 + (1 / v) ^ k) := by
          have := pow_nonneg (le_of_lt hv') k
          gcongr
          linarith
  · have h1 : 1 + 1 / v ≤ 2 := by linarith
    calc (1 + 1 / v) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) h1 k
      _ ≤ 2 ^ k * (1 + (1 / v) ^ k) := by
          have h2 : (0:ℝ) < 2 ^ k := by positivity
          have h3 : (0:ℝ) ≤ (1 / v) ^ k := pow_nonneg (le_of_lt hv') k
          nlinarith

/-- The arithmetic of the abelian cardinality bound. -/
lemma abelian_arith (m r s : ℕ) (v : ℝ) (hv : 0 < v) (hrs : 2 * r + s ≤ m) :
    2 ^ s * (1 + 2 * Real.pi * r / v) ^ r
      ≤ 2 ^ m * (2 ^ (m / 2) * (1 + 2 * Real.pi * m) ^ (m / 2))
        * (1 + v ^ (-(m / 2 : ℕ) : ℤ)) := by
  have hrk : r ≤ m / 2 := by omega
  have hsle : s ≤ m := by omega
  have hrm : (r : ℝ) ≤ (m : ℝ) := by
    have : r ≤ m := by omega
    exact_mod_cast this
  have hbase1 : (1 : ℝ) ≤ 1 + 2 * Real.pi * r / v := by
    have : (0 : ℝ) ≤ 2 * Real.pi * r / v := by positivity
    linarith
  have hbase1' : (1 : ℝ) ≤ 1 + 2 * Real.pi * m / v := by
    have : (0 : ℝ) ≤ 2 * Real.pi * m / v := by positivity
    linarith
  have hstep1 : (1 + 2 * Real.pi * r / v) ^ r ≤ (1 + 2 * Real.pi * m / v) ^ (m / 2) := by
    have hle : 1 + 2 * Real.pi * r / v ≤ 1 + 2 * Real.pi * m / v := by
      have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
      have : 2 * Real.pi * r ≤ 2 * Real.pi * m := by nlinarith
      have : 2 * Real.pi * r / v ≤ 2 * Real.pi * m / v := by gcongr
      linarith
    exact le_trans (pow_le_pow_left₀ (by positivity) hle r) (pow_le_pow_right₀ hbase1' hrk)
  have hstep2 : (1 + 2 * Real.pi * m / v) ^ (m / 2)
      ≤ ((1 + 2 * Real.pi * m) * (1 + 1 / v)) ^ (m / 2) := by
    have hle : 1 + 2 * Real.pi * m / v ≤ (1 + 2 * Real.pi * m) * (1 + 1 / v) := by
      have h1 : (0 : ℝ) ≤ 2 * Real.pi * m := by positivity
      have h2 : (0 : ℝ) ≤ 1 / v := by positivity
      calc 1 + 2 * Real.pi * m / v
          ≤ 1 + 2 * Real.pi * m + 1 / v + 2 * Real.pi * m / v := by linarith
        _ = (1 + 2 * Real.pi * m) * (1 + 1 / v) := by ring
    exact pow_le_pow_left₀ (by positivity) hle (m / 2)
  have hstep4 : (1 + 1 / v) ^ (m / 2) ≤ 2 ^ (m / 2) * (1 + (1 / v) ^ (m / 2)) :=
    pow_one_add_inv_le v hv (m / 2)
  have h2s : (2 : ℝ) ^ s ≤ 2 ^ m :=
    pow_le_pow_right₀ (by norm_num) hsle
  have hzpow : v ^ (-(m / 2 : ℕ) : ℤ) = (1 / v) ^ (m / 2) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, one_div]
  calc 2 ^ s * (1 + 2 * Real.pi * r / v) ^ r
      ≤ 2 ^ m * (1 + 2 * Real.pi * m / v) ^ (m / 2) := by
        exact mul_le_mul h2s hstep1 (by positivity) (by positivity)
    _ ≤ 2 ^ m * (((1 + 2 * Real.pi * m) * (1 + 1 / v)) ^ (m / 2)) := by
        exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = 2 ^ m * ((1 + 2 * Real.pi * m) ^ (m / 2) * (1 + 1 / v) ^ (m / 2)) := by rw [mul_pow]
    _ ≤ 2 ^ m * ((1 + 2 * Real.pi * m) ^ (m / 2)
          * (2 ^ (m / 2) * (1 + (1 / v) ^ (m / 2)))) := by
        gcongr
    _ = 2 ^ m * (2 ^ (m / 2) * (1 + 2 * Real.pi * m) ^ (m / 2))
          * (1 + (1 / v) ^ (m / 2)) := by ring
    _ = 2 ^ m * (2 ^ (m / 2) * (1 + 2 * Real.pi * m) ^ (m / 2))
          * (1 + v ^ (-(m / 2 : ℕ) : ℤ)) := by rw [hzpow]

/-- **Cardinality bound for a finite abelian subgroup of `O(m)`.**  A finite abelian
`A ≤ O(m)` whose non-identity elements satisfy `v ≤ rotN` has at most
`C * (1 + v ^ (-⌊m/2⌋))` elements.

Route: `Work.Mostow.abelianBlockStructure` writes `A` by characters `χ i : A →* Circle`
(`i : Fin r`) and signs `τ j : A →* Multiplicative (ZMod 2)` (`j : Fin s`), with `2r + s ≤ m`,
jointly injective and with `rotN a ≤ ∑ i, ‖χ i a - 1‖ + ∑ j, [...]`.  The arguments
`arg (χ i ·)` are additive homomorphisms `A → ℝ/2πℤ`, so on the kernel `K` of the sign map
they realise `K` as a finite subgroup of the torus `(ℝ/2πℤ)^r` in which every nonzero element has
a coordinate of norm `≥ v/r` (because `2 |sin (θ/2)| ≤ θ ≤ rotN`); box counting gives
`|K| ≤ (1 + 2πr/v)^r`, and `|A| ≤ 2^s |K|`.  Then `r ≤ ⌊m/2⌋`, `s ≤ m` and
`(1 + 2πr/v)^r ≤ (1 + 2πm)^{⌊m/2⌋} 2^{⌊m/2⌋} (1 + v^{-⌊m/2⌋})`. -/
theorem abelianCardBound (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Subgroup (E m ≃ₗᵢ[ℝ] E m)) [Finite A] (v : ℝ), 0 < v →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ≠ 1 → v ≤ rotN a) →
      (Nat.card A : ℝ) ≤ C * (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ)) := by
  refine ⟨2 ^ m * (2 ^ (m / 2) * (1 + 2 * Real.pi * m) ^ (m / 2)), by positivity, ?_⟩
  intro A hAfin v hv hcomm hsep
  haveI : Fintype A := Fintype.ofFinite A
  obtain ⟨r, s, χ, τ, hrs, hinj, hnorm⟩ := abelianBlockStructure m A hcomm
  -- the torus data
  let ψ : A → (Fin r → AddCircle (2 * Real.pi)) :=
    fun a i => ((Complex.arg ((χ i a : Circle) : ℂ) : ℝ) : AddCircle (2 * Real.pi))
  let σ : A → (Fin s → ZMod 2) := fun a j => if τ j a = 1 then 0 else 1
  have hψ1 : ψ 1 = 0 := by
    funext i
    simp [ψ]
  have hσ1 : σ 1 = 0 := by
    funext j
    simp [σ]
  have hψadd : ∀ a b : A, ψ (a * b) = ψ a + ψ b := by
    intro a b
    funext i
    simp only [ψ, Pi.add_apply]
    rw [map_mul]
    exact arg_coe_mul_add (χ i a) (χ i b)
  have hσadd : ∀ a b : A, σ (a * b) = σ a + σ b := by
    intro a b
    funext j
    simp only [σ, Pi.add_apply]
    rw [map_mul]
    exact zmod2_indicator_mul (τ j a) (τ j b)
  have hargZero : ∀ (a : A) (i : Fin r), ψ a i = 0 → Complex.arg ((χ i a : Circle) : ℂ) = 0 := by
    intro a i h
    have h2 := norm_arg_coe (χ i a)
    have h' : ((Complex.arg ((χ i a : Circle) : ℂ) : ℝ) : AddCircle (2 * Real.pi)) = 0 := h
    rw [h'] at h2
    have h3 : |Complex.arg ((χ i a : Circle) : ℂ)| = 0 := by simpa using h2.symm
    exact abs_eq_zero.mp h3
  have hψinj : ∀ a : A, ψ a = 0 → (∀ i, χ i a = 1) := by
    intro a hψ i
    exact circle_eq_one_of_arg_eq_zero (χ i a) (hargZero a i (congrFun hψ i))
  have hσinj : ∀ a : A, σ a = 0 → (∀ j, τ j a = 1) := by
    intro a hσ j
    by_contra hne
    have h := congrFun hσ j
    simp only [σ, Pi.zero_apply] at h
    rw [if_neg hne] at h
    exact one_ne_zero h
  have hinjT : ∀ a : A, ψ a = 0 → σ a = 0 → a = 1 := fun a hψ hσ =>
    hinj a (hψinj a hψ) (hσinj a hσ)
  have hnormT : ∀ a : A, σ a = 0 → rotN (a : E m ≃ₗᵢ[ℝ] E m) ≤ ∑ i : Fin r, ‖ψ a i‖ := by
    intro a hσa
    show ‖((a : A) : E m →L[ℝ] E m) - 1‖ ≤ ∑ i : Fin r, ‖ψ a i‖
    have h1 := hnorm a
    have h2 : (∑ i : Fin r, ‖(((χ i a) : Circle) : ℂ) - 1‖) ≤ ∑ i : Fin r, ‖ψ a i‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact norm_sub_one_le_norm_arg (χ i a)
    have h3 : (∑ j : Fin s, (if τ j a = 1 then (0 : ℝ) else 2)) = 0 := by
      have hall : ∀ j : Fin s, τ j a = 1 := hσinj a hσa
      simp [hall]
    linarith
  have hmain : (Nat.card A : ℝ) ≤ 2 ^ s * (1 + 2 * Real.pi * r / v) ^ r :=
    card_le_of_torusData A hv hsep hrs ψ σ hψ1 hσ1 hψadd hσadd hinjT hnormT
  exact le_trans hmain (abelian_arith m r s v hv hrs)

/-! ## The target theorem -/

/-- **G4 of the strata chapter**: a finite subgroup of `O(m)` that is `v`-separated from `1` has at
most `J * v ^ (-(m/2))` elements (with `J` depending only on `m`).

`Work.Mostow.exists_abelian_subgroup_index` produces an abelian subgroup `B` of bounded index,
`Work.Mostow.abelianCardBound` bounds `|B|`, and the two combine. -/
theorem cardKernelTorus (m : ℕ) : ∃ J : ℝ, 0 < J ∧ ∀ (A : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)) [Finite A] (v : ℝ), 0 < v → (∀ a ∈ A, a ≠ 1 → v ≤ Submission.Mostow.rotN a) → (Nat.card A : ℝ) ≤ J * (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ)) := by
  obtain ⟨J₀, hJ₀pos, hJ₀⟩ := exists_abelian_subgroup_index m
  obtain ⟨C, hCpos, hC⟩ := abelianCardBound m
  refine ⟨J₀ * C, mul_pos hJ₀pos hCpos, ?_⟩
  intro A hAfin v hv hsep
  obtain ⟨B, hBab, hBcard⟩ := hJ₀ A
  haveI : Finite B := Subtype.finite
  set B' : Subgroup (E m ≃ₗᵢ[ℝ] E m) := B.map (Subgroup.subtype A) with hB'
  have hcardB' : Nat.card B' = Nat.card B := by
    rw [hB', Subgroup.card_map_of_injective Subtype.coe_injective]
  have hcomm' : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    rw [hB'] at ha hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg (fun z : A => (z : E m ≃ₗᵢ[ℝ] E m)) (hBab x hx y hy)
  have hsep' : ∀ a ∈ B', a ≠ 1 → v ≤ Submission.Mostow.rotN a := by
    intro a ha ha1
    rw [hB'] at ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hx1 : x ≠ 1 := by
      intro h
      exact ha1 (by rw [h]; rfl)
    have hx1' : ((x : A) : E m ≃ₗᵢ[ℝ] E m) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact hsep ((x : A) : E m ≃ₗᵢ[ℝ] E m) x.2 hx1'
  haveI hB'fin : Finite B' := by
    rw [hB']
    exact Finite.of_surjective
      (fun x : B => (⟨A.subtype x, Subgroup.mem_map_of_mem A.subtype x.2⟩ :
        ↥(Subgroup.map A.subtype B)))
      (fun y => by
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)
  have hle := hC B' v hv hcomm' hsep'
  rw [hcardB'] at hle
  calc (Nat.card A : ℝ) ≤ J₀ * (Nat.card B : ℝ) := hBcard
    _ ≤ J₀ * (C * (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ))) := by
        gcongr
    _ = J₀ * C * (1 + (v : ℝ) ^ (-(m / 2 : ℕ) : ℤ)) := by ring

end

end Work.Mostow
