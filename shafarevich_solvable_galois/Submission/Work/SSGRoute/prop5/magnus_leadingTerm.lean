import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.SSGRoute.prop5.lowerCentralSeries_torsionFree
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnus_unitCongr_isolated
import Submission.Work.SSGRoute.prop5.magnus_detects_gamma
import Submission.Work.SSGRoute.prop5.adjacent.magnus_image_saturated
import Submission.Work.SSGRoute.prop5.adjacent_pSeries_inter_lcs_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus "leading term" detects `p`-th powers modulo the next lower central term

Let `F = FreeGroup X` be a free group with lower central series `γ_n` and let
`magnus X N : F →* (FreeAssoc X ⧸ fil X N)ˣ` be the (truncated) Magnus map into the units of the
free associative `ℤ`-algebra modulo the ideal of words of length `≥ N`.  In Mathlib's indexing
`(⊤ : Subgroup F).lowerCentralSeries n` is the paper's `γ_{n+1}`.

The main theorem of this file (`magnus_leadingTerm`) proves: if `z` lies in the paper's `γ_j` and
the *leading term* of the Magnus image of `z` (its component in the degree-`j` part of the
truncated algebra) is divisible by `p`, then `z` is a `p`-th power of an element of `γ_j` modulo
`γ_{j+1}`:

`z ∈ ⟨γ_j^p⟩ · γ_{j+1}`.

The proof has an elementary part, done here, and two classical inputs, isolated as hypotheses of
the assembly lemma `magnus_leadingTerm_of_kernel_and_pure`:

* `hkernel` : the Magnus map *detects* the lower central series (kernel form), i.e. an element of
  `γ_j` whose Magnus image is `≡ 1` modulo `fil (j+1)` lies in `γ_{j+1}` — the "hard half" of the
  Magnus embedding theorem (Magnus 1935, Witt 1937), the converse of the already available
  `magnus_mem_one_add`;
* `hpure` : the image of `γ_j` in the degree-`j` part is *pure* (saturated): if a positive multiple
  of `x` lies in the image, so does `x` itself — equivalently the degree-`j` part of the free Lie
  ring is a direct summand of the degree-`j` part of the free associative algebra.

The elementary part shows that the leading term map
`z ↦ magLT z = (magnus X (j+1) z : R) - 1 ∈ R` (for `R = FreeAssoc X ⧸ fil X (j+1)`) is a
homomorphism of `γ_j` into the additive group of the degree-`j` part, and that it converts
`p`-th powers into multiplication by `p`: `magLT (w^p) = p * magLT w`.  Hence divisibility of the
leading term of `z` by `p` produces a `p`-th power congruent to `z` modulo `γ_{j+1}`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-! ## Elementary facts about the truncated algebra -/

/-- The `N`-th filtration piece of `FreeAssoc X ⧸ fil X N` is zero. -/
theorem filq_self_eq_bot (X : Type*) (N : ℕ) : filq X N N = ⊥ := by
  rw [filq, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

theorem mem_filq_self_eq_zero {N : ℕ} {x : FreeAssoc X ⧸ fil X N} (h : x ∈ filq X N N) :
    x = 0 := by
  rw [filq_self_eq_bot] at h
  exact h

/-- The product of two elements of the degree-`j` part of `FreeAssoc X ⧸ fil X (j+1)` vanishes
(for `j ≥ 1`): the degree-`j` part has square zero. -/
theorem mul_self_eq_zero_of_mem_filq (j : ℕ) (hj : 1 ≤ j) {x : FreeAssoc X ⧸ fil X (j + 1)}
    (hx : x ∈ filq X (j + 1) j) : x * x = 0 :=
  mem_filq_self_eq_zero (filq_antitone X (j + 1) (by omega)
    (mul_mem_filq X (j + 1) j j hx hx))

/-! ## The leading term of the Magnus image -/

/-- The Magnus image of `z`, transported to the ring `FreeAssoc X ⧸ fil X (j+1)` and shifted by
`1`.  For `z` in the paper's `γ_j` this is the "degree-`j` leading term" of `z`. -/
-- dedup 10-05: `magLT` is no longer declared here; it is imported from
-- `prop5.adjacent_pSeries_inter_lcs_le` (same body: `((magnus X (j+1) z : Rˣ) : R) - 1`).
-- def magLT (X : Type*) (j : ℕ) (z : FreeGroup X) : FreeAssoc X ⧸ fil X (j + 1) :=
--   ((magnus X (j + 1) z : (FreeAssoc X ⧸ fil X (j + 1))ˣ) : FreeAssoc X ⧸ fil X (j + 1)) - 1

@[simp]
theorem magLT_one (X : Type*) (j : ℕ) : magLT X j 1 = 0 := by
  simp [magLT]

/-- The "easy half" of the Magnus embedding gives that the leading term of an element of the
paper's `γ_j` lies in the degree-`j` part. -/
theorem magLT_mem_filq (X : Type*) (j : ℕ) (hj : 1 ≤ j) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    magLT X j z ∈ filq X (j + 1) j := by
  have h := magnus_mem_one_add X (j + 1) (j - 1) (by omega) z hz
  rwa [show j - 1 + 1 = j from by omega] at h

/-- The leading term vanishes on the paper's `γ_{j+1}`. -/
theorem magLT_eq_zero_of_mem_succ (X : Type*) (j : ℕ) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j) : magLT X j z = 0 := by
  have h := magnus_mem_one_add X (j + 1) j (by omega) z hz
  unfold magLT
  exact mem_filq_self_eq_zero h

/-- **The leading term is additive on `γ_j`.**  For `g`, `h` in the paper's `γ_j` the degree-`j`
part of the Magnus image of `g * h` is the sum of the degree-`j` parts: the cross term lies in
`filq (2j) ⊆ filq (j+1)`, which is zero in the truncated algebra. -/
theorem magLT_mul (X : Type*) (j : ℕ) (hj : 1 ≤ j) {g h : FreeGroup X}
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (hh : h ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    magLT X j (g * h) = magLT X j g + magLT X j h := by
  have hsq : magLT X j g * magLT X j h = 0 :=
    mem_filq_self_eq_zero (filq_antitone X (j + 1) (by omega)
      (mul_mem_filq X (j + 1) j j (magLT_mem_filq X j hj hg) (magLT_mem_filq X j hj hh)))
  have key : magLT X j (g * h)
      = magLT X j g + magLT X j h + magLT X j g * magLT X j h := by
    unfold magLT
    rw [map_mul, Units.val_mul]
    noncomm_ring
  rw [key, hsq, add_zero]

/-- The leading term of the inverse. -/
theorem magLT_inv (X : Type*) (j : ℕ) (hj : 1 ≤ j) {w : FreeGroup X}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    magLT X j w⁻¹ = -magLT X j w := by
  have h1 : magLT X j (w * w⁻¹) = 0 := by rw [mul_inv_cancel]; exact magLT_one X j
  have h2 := magLT_mul X j hj hw (Subgroup.inv_mem _ hw)
  rw [h1] at h2
  have h3 : magLT X j w⁻¹ + magLT X j w = 0 := by
    rw [add_comm (magLT X j w⁻¹) (magLT X j w)]
    exact h2.symm
  exact eq_neg_of_add_eq_zero_left h3

/-- **The leading term converts `p`-th powers into multiplication by `p`.**  Since the degree-`j`
part has square zero, `(1 + u)^p = 1 + p * u` in the truncated algebra, which is the assertion. -/
theorem magLT_pow (X : Type*) (j : ℕ) (hj : 1 ≤ j) (p : ℕ) {w : FreeGroup X}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) :
    magLT X j (w ^ p) = (p : ℤ) * magLT X j w := by
  have hsq : magLT X j w * magLT X j w = 0 := mul_self_eq_zero_of_mem_filq j hj
    (magLT_mem_filq X j hj hw)
  have key : magLT X j (w ^ p) = (1 + magLT X j w) ^ p - 1 := by
    unfold magLT
    rw [map_pow, Units.val_pow_eq_pow_val]
    rw [show (1 : FreeAssoc X ⧸ fil X (j + 1)) +
        (((magnus X (j + 1) w : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
          FreeAssoc X ⧸ fil X (j + 1)) - 1)
        = ((magnus X (j + 1) w : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
          FreeAssoc X ⧸ fil X (j + 1)) from by noncomm_ring]
  rw [key, one_add_pow_eq_of_sq_zero (magLT X j w) hsq p, add_sub_cancel_left]
  exact nsmul_eq_mul p (magLT X j w)

/-! ## The assembly -/

/-- **Assembly.**  Assume the two classical inputs

* `hkernel`: the Magnus map detects the lower central series (`γ_j ∩ ker = γ_{j+1}`), and
* `hpure`: the Magnus image of `γ_j` in the degree-`j` part is pure.

Then a `p`-divisible leading term of `z ∈ γ_j` forces `z ∈ ⟨γ_j^p⟩ · γ_{j+1}`.

Indeed the leading term map is additive on `γ_j` and sends `p`-th powers to `p`-multiples, so
purity turns `magLT z = p * a` into `magLT z = p * magLT w = magLT (w^p)` for some `w ∈ γ_j`;
then `z * (w^p)⁻¹` has vanishing leading term, hence lies in `γ_{j+1}` by `hkernel`. -/
theorem magnus_leadingTerm_of_kernel_and_pure
    (hkernel : ∀ (Y : Type) (j : ℕ), 1 ≤ j →
      ∀ y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
        ((magnus Y (j + 1) y : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
            FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = 0 →
        y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries j)
    (hpure : ∀ (Y : Type) (n j : ℕ), 0 < n → 1 ≤ j →
      ∀ y ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
      ∀ x : FreeAssoc Y ⧸ fil Y (j + 1), x ∈ filq Y (j + 1) j →
        ((magnus Y (j + 1) y : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
            FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = (n : ℤ) * x →
        ∃ w ∈ (⊤ : Subgroup (FreeGroup Y)).lowerCentralSeries (j - 1),
          ((magnus Y (j + 1) w : (FreeAssoc Y ⧸ fil Y (j + 1))ˣ) :
              FreeAssoc Y ⧸ fil Y (j + 1)) - 1 = x)
    (p : ℕ) (hp : 0 < p) (X : Type) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup X)
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (h : ∃ a : FreeAssoc X ⧸ fil X (j + 1),
          a ∈ Ideal.map (Ideal.Quotient.mk (fil X (j + 1))) (fil X j) ∧
          ((magnus X (j + 1) z : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
              FreeAssoc X ⧸ fil X (j + 1)) - 1 = (p : ℤ) * a) :
    z ∈ Work.Shrinking.powSubgroup p ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
        ⊔ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
  obtain ⟨a, ha_mem, ha_eq⟩ := h
  -- purity: the leading term of `z` is the leading term of an honest element `w ∈ γ_j`
  obtain ⟨w, hw_mem, hw_eq⟩ := hpure X p j hp hj z hz a ha_mem ha_eq
  have hw' : w ^ p ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.pow_mem _ hw_mem p
  have hz_eq : magLT X j z = (p : ℤ) * a := ha_eq
  have hw_eq' : magLT X j w = a := hw_eq
  have hwp : magLT X j (w ^ p) = (p : ℤ) * a := by
    rw [magLT_pow X j hj p hw_mem, hw_eq']
  have hmem1 : z * (w ^ p)⁻¹ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.mul_mem _ hz (Subgroup.inv_mem _ hw')
  have hzero : magLT X j (z * (w ^ p)⁻¹) = 0 := by
    rw [magLT_mul X j hj hz (Subgroup.inv_mem _ hw'), magLT_inv X j hj hw', hwp, hz_eq]
    exact add_neg_cancel _
  have hker := hkernel X j hj (z * (w ^ p)⁻¹) hmem1 hzero
  have hdecomp : z = (z * (w ^ p)⁻¹) * (w ^ p) := by group
  rw [hdecomp]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hker) (Subgroup.mem_sup_left ?_)
  exact Subgroup.subset_closure ⟨w, hw_mem, rfl⟩

theorem magnus_leadingTerm (p : ℕ) [Fact p.Prime] (X : Type) (j : ℕ) (hj : 1 ≤ j) (z : FreeGroup X)
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (h : ∃ a : FreeAssoc X ⧸ fil X (j + 1),
          a ∈ Ideal.map (Ideal.Quotient.mk (fil X (j + 1))) (fil X j) ∧
          ((magnus X (j + 1) z : (FreeAssoc X ⧸ fil X (j + 1))ˣ) :
              FreeAssoc X ⧸ fil X (j + 1)) - 1 = (p : ℤ) * a) :
    z ∈ Work.Shrinking.powSubgroup p ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
        ⊔ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j :=
  magnus_leadingTerm_of_kernel_and_pure
    (fun Y j hj y hy h => magnus_detects_gamma Y j hj y hy h)
    (fun Y n j hn hj y hy x hx h =>
      Work.SSGRoute.prop5.adjacent.magnus_image_saturated Y n j hn hj y hy x hx h)
    p (Fact.out : p.Prime).pos X j hj z hz h

end Work.SSGRoute.prop5
