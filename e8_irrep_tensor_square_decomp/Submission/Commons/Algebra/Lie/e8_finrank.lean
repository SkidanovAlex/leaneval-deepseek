import Mathlib
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_W_le_Psub
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_W_eq_bot_of_not_cone
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_root_weightSpace_finrank_eq_one
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_rootVector_card
import Submission.Commons.Algebra.Lie.SerreConstruction.exists_finset_e8_roots
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_weightSpace_iSup_eq_top
import Submission.Commons.LinearAlgebra.Submodule.rank_iSup_eq_sum_of_iSupIndep
import Submission.Commons.LinearAlgebra.Eigenspace.iSupIndep_eigenspace_of_commute_of_torsionfree
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef

open scoped BigOperators Matrix
noncomputable section

namespace Commons.Algebra.Lie
open Commons.Algebra.Lie.SerreConstruction

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 1600000

/-- The Weyl invariant squared length `(μ,μ) = μᵀA⁻¹μ` (with `A = E₈`). -/
def e8Nrm (μ : Fin 8 → ℤ) : ℚ :=
  ∑ i, ∑ j, (μ i : ℚ) * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (μ j : ℚ)

/-- The weight space of `e₈(ℂ)` at an integral weight. -/
def e8W (μ : Fin 8 → ℤ) : Submodule ℂ (LieAlgebra.e₈ ℂ) := wtSpace μ

lemma e8W_eq_W (μ : Fin 8 → ℤ) : e8W μ = W (fun i => (μ i : ℂ)) := rfl

lemma e8W_eq_wtSpace (μ : Fin 8 → ℤ) : e8W μ = wtSpace μ := rfl
/-- The weight `∑ nᵢαᵢ` in `ω`-coordinates. -/
def wcoord (n : Fin 8 → ℤ) : Fin 8 → ℤ := fun j => ∑ i, CartanMatrix.E₈ j i * n i

lemma wcoord_add (m n : Fin 8 → ℤ) : wcoord (m + n) = wcoord m + wcoord n := by
  funext j
  simp only [wcoord, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma wcoord_zsmul (k : ℤ) (m : Fin 8 → ℤ) : wcoord (k • m) = k • wcoord m := by
  funext j
  simp only [wcoord, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma wcoord_single (i : Fin 8) : wcoord (Pi.single i 1) = fun j => CartanMatrix.E₈ j i := by
  funext j
  simp only [wcoord, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i (fun x => CartanMatrix.E₈ j x)]
  simp

lemma wcoord_sub (m n : Fin 8 → ℤ) : wcoord (m - n) = wcoord m - wcoord n := by
  rw [sub_eq_add_neg, show -(n : Fin 8 → ℤ) = (-1 : ℤ) • n from (neg_one_smul ℤ n).symm,
    wcoord_add, wcoord_zsmul, sub_eq_add_neg]
  simp

/-- The bilinear form with matrix `A = E₈`. -/
def qpair (m n : Fin 8 → ℤ) : ℚ :=
  ∑ i, ∑ j, (m i : ℚ) * (CartanMatrix.E₈ i j : ℚ) * (n j : ℚ)

/-- The quadratic form `m ↦ mᵀAm`. -/
def qform (m : Fin 8 → ℤ) : ℚ := qpair m m

lemma E8_cast_symm (i j : Fin 8) :
    (CartanMatrix.E₈ i j : ℚ) = (CartanMatrix.E₈ j i : ℚ) := by
  exact_mod_cast E8_symm i j

lemma qpair_eq (m n : Fin 8 → ℤ) : qpair m n = ∑ i, (m i : ℚ) * (wcoord n i : ℚ) := by
  simp only [qpair, wcoord]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma qpair_symm (m n : Fin 8 → ℤ) : qpair m n = qpair n m := by
  simp only [qpair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [E8_cast_symm j i]
  ring

lemma qpair_single (m : Fin 8 → ℤ) (i : Fin 8) :
    qpair m (Pi.single i 1) = (wcoord m i : ℚ) := by
  rw [qpair_eq, wcoord_single]
  rw [show (wcoord m i : ℚ) = ∑ p, (CartanMatrix.E₈ i p : ℚ) * (m p : ℚ) from by
    simp only [wcoord]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by ring]
  exact Finset.sum_congr rfl fun p _ => by rw [E8_cast_symm i p]; ring

lemma qpair_single_single (i j : Fin 8) :
    qpair (Pi.single i 1) (Pi.single j 1) = (CartanMatrix.E₈ i j : ℚ) := by
  rw [qpair_eq, wcoord_single]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]; ring
  · intro b _ hb; rw [Pi.single_eq_of_ne (M := fun _ => ℤ) hb]; ring
  · intro h; exact absurd (Finset.mem_univ i) h

lemma qpair_add_right (m n n' : Fin 8 → ℤ) : qpair m (n + n') = qpair m n + qpair m n' := by
  rw [qpair_eq, qpair_eq, qpair_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wcoord_add, Pi.add_apply]
  push_cast
  ring

lemma qpair_add_left (m m' n : Fin 8 → ℤ) : qpair (m + m') n = qpair m n + qpair m' n := by
  rw [qpair_symm (m + m') n, qpair_add_right, qpair_symm n m, qpair_symm n m']

lemma qpair_zsmul_right (m n : Fin 8 → ℤ) (k : ℤ) :
    qpair m (k • n) = (k : ℚ) * qpair m n := by
  rw [qpair_eq, qpair_eq, wcoord_zsmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma qpair_zsmul_left (m n : Fin 8 → ℤ) (k : ℤ) :
    qpair (k • m) n = (k : ℚ) * qpair m n := by
  rw [qpair_symm (k • m) n, qpair_zsmul_right, qpair_symm n m]

/-- **The quadratic form is invariant under the simple reflection** `m ↦ m - (Am)ᵢ eᵢ`. -/
lemma qform_add (a b : Fin 8 → ℤ) : qform (a + b) = qform a + 2 * qpair a b + qform b := by
  rw [qform, qpair_add_left, qpair_add_right, qpair_add_right, qpair_symm b a, qform, qform]
  ring

/-- **The quadratic form is invariant under the simple reflection** `m ↦ m - (Am)ᵢ eᵢ`. -/
lemma qform_smul_single (k : ℤ) (i : Fin 8) :
    qform (k • Pi.single i 1) = 2 * (k : ℚ) ^ 2 := by
  rw [qform, qpair_zsmul_left, qpair_zsmul_right, qpair_single_single,
    show CartanMatrix.E₈ i i = 2 from E8_diag i]
  ring

lemma qform_reflect (m : Fin 8 → ℤ) (i : Fin 8) :
    qform (m - (wcoord m i) • Pi.single i 1) = qform m := by
  have hsplit : m - (wcoord m i) • Pi.single i 1
      = m + ((-(wcoord m i)) • Pi.single i 1) := by
    rw [neg_smul]; abel
  rw [hsplit, qform_add, qpair_zsmul_right, qpair_single, qform_smul_single]
  push_cast
  ring


lemma eq_zero_of_sum_eq_zero {m : Fin 8 → ℕ} (h : ∑ i, m i = 0) : m = 0 := by
  funext i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le (m i))).mp h i (Finset.mem_univ i)

lemma one_le_sum_of_ne_zero {m : Fin 8 → ℕ} (hm : m ≠ 0) : 1 ≤ ∑ i, m i := by
  by_contra h
  push_neg at h
  exact hm (eq_zero_of_sum_eq_zero (by omega))

/-- The span of all brackets `⁅u, v⁆` with `u ∈ M`, `v ∈ N`. -/
def Sbrk (M N : Submodule ℂ L8) : Submodule ℂ L8 :=
  Submodule.span ℂ {x : L8 | ∃ u ∈ M, ∃ v ∈ N, ⁅u, v⁆ = x}

lemma mem_Sbrk {M N : Submodule ℂ L8} {u v : L8} (hu : u ∈ M) (hv : v ∈ N) :
    ⁅u, v⁆ ∈ Sbrk M N :=
  Submodule.subset_span ⟨u, hu, v, hv, rfl⟩

lemma Sbrk_mono {M M' N N' : Submodule ℂ L8} (hM : M ≤ M') (hN : N ≤ N') :
    Sbrk M N ≤ Sbrk M' N' := by
  rw [Sbrk, Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  exact mem_Sbrk (hM hu) (hN hv)

/-- The "derived" part at degree `n`: brackets of two nonzero lower degree pieces. -/
def Dpart (n : Fin 8 → ℕ) : Submodule ℂ L8 :=
  ⨆ (p : (Fin 8 → ℕ) × (Fin 8 → ℕ)) (_ : p.1 + p.2 = n) (_ : p.1 ≠ 0) (_ : p.2 ≠ 0),
    Sbrk (Pm p.1) (Pm p.2)

lemma Dpart_le_Pm (n : Fin 8 → ℕ) : Dpart n ≤ Pm n := by
  rw [Dpart]
  refine iSup_le fun p => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 => ?_
  rw [Sbrk, Submodule.span_le]
  rintro x ⟨u, hu, v, hv, rfl⟩
  rw [← h1]
  exact bracket_mem_Pm hu hv

/-- The approximation to `Psub` generated by the degree-one pieces together with all brackets
of two nonzero pieces. -/
def Zf (n : Fin 8 → ℕ) : Submodule ℂ L8 :=
  if (∑ i, n i) = 0 then ⊥ else if (∑ i, n i) = 1 then Pm n else Dpart n

@[simp] lemma Zf_zero : Zf 0 = ⊥ := by
  rw [Zf]; simp

lemma Zf_le_Pm (n : Fin 8 → ℕ) : Zf n ≤ Pm n := by
  rw [Zf]
  split_ifs with h0 h1
  · exact bot_le
  · exact le_rfl
  · exact Dpart_le_Pm n

lemma Sbrk_le_Zf (m m' : Fin 8 → ℕ) (hm : m ≠ 0) (hm' : m' ≠ 0) :
    Sbrk (Pm m) (Pm m') ≤ Zf (m + m') := by
  have h2 : 2 ≤ ∑ i, (m + m') i := by
    have hm1 := one_le_sum_of_ne_zero hm
    have hm1' := one_le_sum_of_ne_zero hm'
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    omega
  rw [Zf]
  split_ifs with h0 h1
  · omega
  · omega
  · rw [Dpart]
    exact le_iSup_of_le (m, m') (le_iSup_of_le (by simp) (le_iSup_of_le hm (le_iSup_of_le hm'
      le_rfl)))

lemma Zf_lie_mem {m m' : Fin 8 → ℕ} {x y : L8} (hx : x ∈ Zf m) (hy : y ∈ Zf m') :
    ⁅x, y⁆ ∈ Zf (m + m') := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hx0 : x = 0 := by simpa using hx
    rw [hx0, zero_lie]; exact Submodule.zero_mem _
  rcases eq_or_ne m' 0 with rfl | hm'
  · have hy0 : y = 0 := by simpa using hy
    rw [hy0, lie_zero]; exact Submodule.zero_mem _
  exact Sbrk_le_Zf m m' hm hm' (mem_Sbrk (Zf_le_Pm m hx) (Zf_le_Pm m' hy))

lemma NWtSum_injective : Function.Injective NWtSum := by
  intro m n h
  have h1 : (fun i => (m i : ℤ)) = (fun i => (n i : ℤ)) := by
    apply WtSum_injective
    rw [show WtSum (fun i => (m i : ℤ)) = NWtSum m from rfl,
      show WtSum (fun i => (n i : ℤ)) = NWtSum n from rfl, h]
  funext i
  exact_mod_cast congrFun h1 i

/-- The union of the approximating pieces is `Psub`. -/
def Zall : Submodule ℂ L8 := ⨆ n : Fin 8 → ℕ, Zf n

lemma Zall_lie_mem {x y : L8} (hx : x ∈ Zall) (hy : y ∈ Zall) : ⁅x, y⁆ ∈ Zall := by
  refine Submodule.iSup_induction Zf
    (motive := fun x => ∀ y, y ∈ Zall → ⁅x, y⁆ ∈ Zall) hx ?_ ?_ ?_ y hy
  · intro m x hx y hy
    refine Submodule.iSup_induction Zf (motive := fun y => ⁅x, y⁆ ∈ Zall) hy ?_ ?_ ?_
    · intro m' y hy
      exact Submodule.mem_iSup_of_mem (m + m') (Zf_lie_mem hx hy)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
  · intro y hy; rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b ha hb y hy; rw [add_lie]; exact Submodule.add_mem _ (ha y hy) (hb y hy)

lemma Zall_le_Psub : Zall ≤ (Psub : Submodule ℂ L8) := by
  rw [Zall]
  refine iSup_le fun n => ?_
  exact le_trans (Zf_le_Pm n) inf_le_left

lemma Psub_le_Zall : (Psub : Submodule ℂ L8) ≤ Zall := by
  have h : Psub ≤ (⟨Zall, fun hx hy => Zall_lie_mem hx hy⟩ : LieSubalgebra ℂ L8) :=
    LieSubalgebra.lieSpan_le.mpr (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      refine Submodule.mem_iSup_of_mem (Pi.single i 1) ?_
      have h1 : ∑ j : Fin 8, (Pi.single i 1 : Fin 8 → ℕ) j = 1 := by
        rw [Finset.sum_eq_single i]
        · rw [Pi.single_eq_same]
        · intro b _ hb; rw [Pi.single_eq_of_ne (M := fun _ => ℕ) hb]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [Zf, if_neg (by omega), if_pos h1]
      exact SerreE_mem_Pm i)
  exact h

lemma Zall_eq_Psub : Zall = (Psub : Submodule ℂ L8) :=
  le_antisymm Zall_le_Psub Psub_le_Zall

/-- **The graded piece of `Psub` in degree `n` is generated by brackets of the lower pieces.** -/
theorem Pm_eq_Zf (n : Fin 8 → ℕ) : Pm n = Zf n := by
  classical
  refine le_antisymm ?_ (Zf_le_Pm n)
  intro x hx
  have hxP : x ∈ (Psub : Submodule ℂ L8) := hx.1
  have hxZ : x ∈ Zall := by rw [Zall_eq_Psub]; exact hxP
  rw [Zall, Submodule.mem_iSup_iff_exists_finset] at hxZ
  obtain ⟨s, hs⟩ := hxZ
  obtain ⟨f, hf, hsum⟩ := mem_iSup_finset_iff.mp hs
  have hwt : ∀ m ∈ s, f m ∈ W (NWtSum m) := fun m hm => (Zf_le_Pm m (hf m hm)).2
  have hxZ' : (∑ m ∈ s, f m) ∈ W (NWtSum n) := by rw [← hsum]; exact hx.2
  have hk := killer_extract s (fun m => NWtSum m) f hwt hxZ'
  have hxeq : x = ∑ m ∈ s with NWtSum m = NWtSum n, f m := by rw [hsum, hk]
  rw [hxeq, Finset.sum_filter]
  by_cases hn : n ∈ s
  · rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]; exact hf n hn
    · intro b hb hbn
      rw [if_neg]
      intro hc
      exact hbn (NWtSum_injective hc)
    · intro h; exact absurd hn h
  · rw [Finset.sum_eq_zero]
    · exact Submodule.zero_mem _
    · intro b hb
      rw [if_neg]
      intro hc
      exact hn ((NWtSum_injective hc) ▸ hb)

/-- **The graded piece of `Psub` in degree `n` of height at least two is generated by brackets of
lower pieces.** -/
theorem Pm_eq_Dpart (n : Fin 8 → ℕ) (hn : 2 ≤ ∑ i, n i) : Pm n = Dpart n := by
  rw [Pm_eq_Zf, Zf, if_neg (by omega), if_neg (by omega)]

lemma Sbrk_bot_left (N : Submodule ℂ L8) : Sbrk (⊥ : Submodule ℂ L8) N = ⊥ := by
  rw [Sbrk, Submodule.span_eq_bot]
  rintro x ⟨u, hu, v, hv, rfl⟩
  rw [Submodule.mem_bot] at hu
  rw [hu, zero_lie]

lemma Sbrk_bot_right (M : Submodule ℂ L8) : Sbrk M (⊥ : Submodule ℂ L8) = ⊥ := by
  rw [Sbrk, Submodule.span_eq_bot]
  rintro x ⟨u, hu, v, hv, rfl⟩
  rw [Submodule.mem_bot] at hv
  rw [hv, lie_zero]

lemma Sbrk_self_single_eq_bot (i : Fin 8) :
    Sbrk (Pm (Pi.single i 1)) (Pm (Pi.single i 1)) = ⊥ := by
  rw [Sbrk, Submodule.span_eq_bot]
  rintro x ⟨u, hu, v, hv, rfl⟩
  have hu' : u ∈ (ℂ ∙ SerreE i : Submodule ℂ L8) :=
    W_alpha_le_span i (by rw [← NWtSum_single i]; exact hu.2)
  have hv' : v ∈ (ℂ ∙ SerreE i : Submodule ℂ L8) :=
    W_alpha_le_span i (by rw [← NWtSum_single i]; exact hv.2)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu'
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hv'
  rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]

/-- **`Pm` vanishes on the positive multiples of the simple roots of degree at least two.** -/
theorem Pm_smul_single_eq_bot : ∀ k : ℕ, 2 ≤ k → ∀ i : Fin 8, Pm (k • Pi.single i 1) = ⊥ := by
  have key : ∀ k : ℕ, (∀ j ≤ k, 2 ≤ j → ∀ i : Fin 8, Pm (j • Pi.single i 1) = ⊥) := by
    intro k
    induction k with
    | zero => intro j hj h2; omega
    | succ k ih =>
      intro j hj h2 i
      rcases eq_or_lt_of_le hj with hjeq | hlt
      · subst hjeq
        have hsum : ∑ l : Fin 8, ((k + 1) • Pi.single i 1 : Fin 8 → ℕ) l = k + 1 := by
          rw [Finset.sum_eq_single i]
          · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          · intro b _ hb; rw [Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hb, smul_zero]
          · intro h; exact absurd (Finset.mem_univ i) h
        have hsum2 : ∀ m : Fin 8 → ℕ,
            ∑ l : Fin 8, (m • Pi.single i 1 : Fin 8 → ℕ) l = m i := by
          intro m
          rw [Finset.sum_eq_single i]
          · simp [Pi.smul_apply, Pi.single_eq_same]
          · intro b _ hb; simp [Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hb]
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [Pm_eq_Dpart _ (by rw [hsum]; exact h2), Dpart]
        refine le_antisymm ?_ bot_le
        refine iSup_le fun p => iSup_le fun h1 => iSup_le fun h2' => iSup_le fun h3 => ?_
        have hoff1 : ∀ l : Fin 8, l ≠ i → p.1 l = 0 := by
          intro l hl
          have h := congrFun h1 l
          rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hl, smul_zero] at h
          exact (Nat.add_eq_zero.mp h).1
        have hoff2 : ∀ l : Fin 8, l ≠ i → p.2 l = 0 := by
          intro l hl
          have h := congrFun h1 l
          rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hl, smul_zero] at h
          exact (Nat.add_eq_zero.mp h).2
        have hi : p.1 i + p.2 i = k + 1 := by
          have h := congrFun h1 i
          rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
          exact h
        have hp1 : p.1 = p.1 i • Pi.single i 1 := by
          funext l
          by_cases hl : l = i
          · subst hl; simp
          · rw [hoff1 l hl, Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hl, smul_zero]
        have hp2 : p.2 = p.2 i • Pi.single i 1 := by
          funext l
          by_cases hl : l = i
          · subst hl; simp
          · rw [hoff2 l hl, Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hl, smul_zero]
        have hp1sum : ∑ l : Fin 8, p.1 l = p.1 i := by
          conv_lhs => rw [hp1]
          exact hsum2 (p.1 i)
        have hp2sum : ∑ l : Fin 8, p.2 l = p.2 i := by
          conv_lhs => rw [hp2]
          exact hsum2 (p.2 i)
        have hp1i : 1 ≤ p.1 i := by
          have h := one_le_sum_of_ne_zero h2'
          rw [hp1sum] at h
          exact h
        have hp2i : 1 ≤ p.2 i := by
          have h := one_le_sum_of_ne_zero h3
          rw [hp2sum] at h
          exact h
        have hle1 : p.1 i ≤ k := by omega
        have hle2 : p.2 i ≤ k := by omega
        by_cases hc1 : 2 ≤ p.1 i
        · have hbot : Pm p.1 = ⊥ := by rw [hp1]; exact ih (p.1 i) hle1 hc1 i
          rw [hbot]
          exact le_of_eq (Sbrk_bot_left _)
        · have hc1' : p.1 i = 1 := by omega
          by_cases hc2 : 2 ≤ p.2 i
          · have hbot : Pm p.2 = ⊥ := by rw [hp2]; exact ih (p.2 i) hle2 hc2 i
            rw [hbot]
            exact le_of_eq (Sbrk_bot_right _)
          · have hc2' : p.2 i = 1 := by omega
            rw [hp1, hc1', one_smul, hp2, hc2', one_smul]
            exact le_of_eq (Sbrk_self_single_eq_bot i)
      · exact ih j (by omega) h2 i
  exact fun k hk i => key k k le_rfl hk i
-- ----------------------------------------------------------------------------
-- Norm in `n`-coordinates

lemma wcoord_injective : Function.Injective wcoord := by
  intro m n h
  have h1 : wcoord (m - n) = 0 := by
    rw [wcoord_sub, h, sub_self]
  have h2 : qform (m - n) = 0 := by
    rw [qform, qpair_eq]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [show wcoord (m - n) i = 0 from congrFun h1 i]
    ring
  have h3 : m - n = 0 := by
    by_contra hne
    have hne' : (fun i => ((m - n) i : ℚ)) ≠ 0 := by
      intro h0
      apply hne
      funext i
      have := congrFun h0 i
      simp only [Pi.zero_apply] at this
      exact_mod_cast this
    have hpos : 0 < qform (m - n) :=
      Commons.LinearAlgebra.Matrix.Cartan.E8_posDef (fun i => ((m - n) i : ℚ)) hne'
    rw [h2] at hpos
    exact absurd hpos (lt_irrefl 0)
  exact sub_eq_zero.mp h3

lemma e8Nrm_eq_qform (m : Fin 8 → ℤ) : e8Nrm (wcoord m) = qform m := by
  have hdet : IsUnit (CartanMatrix.E₈.map (Int.castRingHom ℚ)).det := by
    have h1 : (CartanMatrix.E₈.map (Int.castRingHom ℚ)).det = 1 := by
      have h2 := RingHom.map_det (Int.castRingHom ℚ) CartanMatrix.E₈
      rw [(show CartanMatrix.E₈.det = 1 from CartanMatrix.E₈_det), map_one] at h2
      exact h2.symm
    rw [h1]
    exact isUnit_one
  have hmul : (CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹
      * (CartanMatrix.E₈.map (Int.castRingHom ℚ)) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hcast : ∀ j : Fin 8, ((wcoord m j : ℤ) : ℚ)
      = ((CartanMatrix.E₈.map (Int.castRingHom ℚ)) *ᵥ (fun i => (m i : ℚ))) j := by
    intro j
    simp only [wcoord, Matrix.mulVec, dotProduct, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
    rfl
  have hkey : ∀ i : Fin 8, (∑ j, ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j
      * ((CartanMatrix.E₈.map (Int.castRingHom ℚ)) *ᵥ (fun i => (m i : ℚ))) j) = (m i : ℚ) := by
    intro i
    have h1 : (∑ j, ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j
        * ((CartanMatrix.E₈.map (Int.castRingHom ℚ)) *ᵥ (fun i => (m i : ℚ))) j)
        = ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹
            *ᵥ (((CartanMatrix.E₈.map (Int.castRingHom ℚ)) *ᵥ (fun i => (m i : ℚ))))) i := rfl
    rw [h1, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  have hmain : ∀ i : Fin 8, (∑ j, (wcoord m i : ℚ)
      * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (wcoord m j : ℚ))
      = (wcoord m i : ℚ) * (m i : ℚ) := by
    intro i
    rw [show (∑ j, (wcoord m i : ℚ)
        * ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j * (wcoord m j : ℚ))
        = (wcoord m i : ℚ) * ∑ j, ((CartanMatrix.E₈.map (Int.castRingHom ℚ))⁻¹) i j
            * ((CartanMatrix.E₈.map (Int.castRingHom ℚ)) *ᵥ (fun i => (m i : ℚ))) j from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcast j]
      ring]
    rw [hkey i]
  rw [e8Nrm, qform, qpair_eq]
  rw [Finset.sum_congr rfl (fun i _ => hmain i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (wcoord m i : ℚ) = ∑ p, (CartanMatrix.E₈ i p : ℚ) * (m p : ℚ) from by
    simp only [wcoord]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by ring]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [E8_cast_symm i p]
  ring

lemma e8Nrm_reflect (i : Fin 8) (m : Fin 8 → ℤ) :
    e8Nrm (wcoord (m - (wcoord m i) • Pi.single i 1)) = e8Nrm (wcoord m) := by
  rw [e8Nrm_eq_qform, e8Nrm_eq_qform, qform_reflect]

lemma exists_pos_of_ne_zero {m : Fin 8 → ℤ} (hm : ∀ i, 0 ≤ m i) (h : m ≠ 0) :
    ∃ i, 1 ≤ m i := by
  by_contra hc
  push_neg at hc
  refine h (funext fun i => ?_)
  simp only [Pi.zero_apply]
  have h1 : m i < 1 := hc i
  have h2 : 0 ≤ m i := hm i
  omega

lemma qform_pos {m : Fin 8 → ℤ} (h : m ≠ 0) : 0 < qform m := by
  have hne' : (fun i => (m i : ℚ)) ≠ 0 := by
    intro h0
    apply h
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply] at this
    exact_mod_cast this
  have hpos := Commons.LinearAlgebra.Matrix.Cartan.E8_posDef (fun i => (m i : ℚ)) hne'
  rwa [show qform m = ∑ i, ∑ j, (m i : ℚ) * (CartanMatrix.E₈ i j : ℚ) * (m j : ℚ) from rfl]
lemma NWtSum_eq_wcoord (m : Fin 8 → ℕ) :
    NWtSum m = fun j => ((wcoord (fun i => (m i : ℤ)) j : ℤ) : ℂ) := by
  funext j
  have h1 : (∑ i, (m i : ℤ) * CartanMatrix.E₈ i j) = wcoord (fun i => (m i : ℤ)) j := by
    simp only [wcoord]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show CartanMatrix.E₈ i j = CartanMatrix.E₈ j i from E8_symm i j, mul_comm]
  simp only [NWtSum, WtSum, alpha]
  rw [show (∑ i, ((m i : ℤ) : ℂ) * ((CartanMatrix.E₈ i j : ℤ) : ℂ))
      = (((∑ i, (m i : ℤ) * CartanMatrix.E₈ i j : ℤ)) : ℂ) from by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring, h1]

/-- An integral weight whose weight space is nonzero lies in one of the two root cones. -/
theorem e8W_cone (μ : Fin 8 → ℤ) (hμ : μ ≠ 0) (h : e8W μ ≠ ⊥) :
    (∃ n : Fin 8 → ℕ, μ = wcoord (fun i => (n i : ℤ))) ∨
    (∃ n : Fin 8 → ℕ, μ = -wcoord (fun i => (n i : ℤ))) := by
  by_contra hc
  push_neg at hc
  refine h (e8_W_eq_bot_of_not_cone (ν := fun i => (μ i : ℂ)) ?_ ?_ ?_)
  · intro hz
    refine hμ (funext fun i => ?_)
    simp only [Pi.zero_apply]
    have h3 : ((μ i : ℤ) : ℂ) = ((0 : ℤ) : ℂ) := by
      have := congrFun hz i
      simpa using this
    exact Int.cast_injective h3
  · intro n hn
    refine hc.1 n ?_
    funext j
    have h1 := congrFun hn.symm j
    rw [NWtSum_eq_wcoord] at h1
    exact Int.cast_injective h1
  · intro n hn
    refine hc.2 n ?_
    funext j
    have h2 : ((μ j : ℤ) : ℂ) = ((-(wcoord (fun i => (n i : ℤ))) j : ℤ) : ℂ) := by
      have h1 := congrFun hn.symm j
      rw [NWtSum_eq_wcoord, Pi.neg_apply] at h1
      simpa using h1
    exact Int.cast_injective h2

/-- The support of the weight decomposition is invariant under the simple reflection. -/
theorem e8W_reflect_ne_bot (i : Fin 8) (μ : Fin 8 → ℤ) (h : e8W μ ≠ ⊥) :
    e8W (fun j => μ j - μ i * CartanMatrix.E₈ i j) ≠ ⊥ := by
  intro hbot
  have hμc : (fun j : Fin 8 => ((fun l => μ l - μ i * CartanMatrix.E₈ i l) j : ℂ))
      = sMu i (fun j : Fin 8 => (μ j : ℂ)) := by
    funext j
    simp only [sMu]
    push_cast
    ring
  have hbot' : W (sMu i (fun j : Fin 8 => (μ j : ℂ))) = ⊥ := by
    rw [← hμc]
    exact hbot
  refine h ?_
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h1 : (reflAut i) x ∈ W (sMu i (fun j : Fin 8 => (μ j : ℂ))) :=
    maps_W i (reflAut i) (reflAut_H i) hx
  rw [hbot'] at h1
  rw [Submodule.mem_bot] at h1
  exact (reflAut i).injective (by simpa using h1)

lemma exists_one_le_of_pos_sum {n : Fin 8 → ℕ} {γ : Fin 8 → ℤ}
    (h : 0 < ∑ j, (n j : ℚ) * (γ j : ℚ)) : ∃ i, 1 ≤ γ i := by
  by_contra hc
  push_neg at hc
  have hle : ∑ j, (n j : ℚ) * (γ j : ℚ) ≤ 0 :=
    Finset.sum_nonpos fun j _ => by
      have h2 : γ j < 1 := hc j
      have h3 : (γ j : ℚ) ≤ 0 := by
        have h4 : γ j ≤ 0 := by omega
        exact_mod_cast h4
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h3
  linarith

lemma sum_wcoord_eq_qform (m : Fin 8 → ℤ) :
    (∑ j, (m j : ℚ) * (wcoord m j : ℚ)) = qform m := by
  rw [qform, qpair_eq]
/-- Reflection invariance of the support, in the form adapted to `wcoord`. -/
theorem e8W_reflect_ne_bot' (i : Fin 8) (μ : Fin 8 → ℤ) (h : e8W μ ≠ ⊥) :
    e8W (fun j => μ j - μ i * CartanMatrix.E₈ j i) ≠ ⊥ := by
  have h1 : (fun j => μ j - μ i * CartanMatrix.E₈ j i)
      = fun j => μ j - μ i * CartanMatrix.E₈ i j := by
    funext j
    rw [show CartanMatrix.E₈ j i = CartanMatrix.E₈ i j from E8_symm j i]
  rw [h1]
  exact e8W_reflect_ne_bot i μ h

lemma wcoord_sub_smul_single (m : Fin 8 → ℤ) (i : Fin 8) :
    wcoord (m - (wcoord m i) • Pi.single i 1)
      = wcoord m - (wcoord m i) • wcoord (Pi.single i 1) := by
  rw [wcoord_sub, wcoord_zsmul]

lemma wcoord_neg (n : Fin 8 → ℤ) : wcoord (-n) = -wcoord n := by
  funext j
  simp only [wcoord, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

lemma wcoord_zero : wcoord 0 = 0 := by
  funext j
  simp [wcoord]

/-- **Positive part.**  If `n` is a nonzero nonnegative vector such that the weight `∑ nᵢαᵢ`
occurs in `e₈`, then `∑ nᵢαᵢ` is a root. -/
theorem e8Nrm_wcoord_of_ne_bot : ∀ N : ℕ, ∀ n : Fin 8 → ℕ, (∑ i, n i) = N → n ≠ 0 →
    e8W (wcoord (fun i => (n i : ℤ))) ≠ ⊥ →
    e8Nrm (wcoord (fun i => (n i : ℤ))) = 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n hsum hn hW
    set m : Fin 8 → ℤ := fun i => (n i : ℤ) with hm
    have hWm : e8W (wcoord m) ≠ ⊥ := hW
    have hm0 : m ≠ 0 := by
      intro hz
      refine hn ?_
      funext i
      simp only [Pi.zero_apply]
      have h1 := congrFun hz i
      have h1' : ((n i : ℕ) : ℤ) = 0 := h1
      omega
    have hpos : 0 < ∑ j, (n j : ℚ) * (wcoord m j : ℚ) := by
      have h1 : (∑ j, (n j : ℚ) * (wcoord m j : ℚ)) = qform m := by
        rw [qform, qpair_eq]
        exact Finset.sum_congr rfl fun j _ => rfl
      rw [h1]
      exact qform_pos hm0
    obtain ⟨i, hi⟩ := exists_one_le_of_pos_sum hpos
    have hreflect : wcoord (m - (wcoord m i) • Pi.single i 1)
        = fun j => wcoord m j - wcoord m i * CartanMatrix.E₈ j i := by
      rw [wcoord_sub_smul_single, wcoord_single]
      funext j
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hWr : e8W (wcoord (m - (wcoord m i) • Pi.single i 1)) ≠ ⊥ :=
      hreflect ▸ e8W_reflect_ne_bot' i (wcoord m) hWm
    have hne : wcoord (m - (wcoord m i) • Pi.single i 1) ≠ 0 := by
      intro hz
      have h1 : wcoord m = (wcoord m i) • wcoord (Pi.single i 1) := by
        have h2 := wcoord_sub_smul_single m i
        rw [h2] at hz
        exact sub_eq_zero.mp hz
      have h3 : wcoord m i = 0 := by
        have h4 := congrFun h1 i
        rw [wcoord_single] at h4
        simp only [Pi.smul_apply, smul_eq_mul] at h4
        rw [show CartanMatrix.E₈ i i = 2 from E8_diag i] at h4
        omega
      have h5 : wcoord m = 0 := by rw [h1, h3, zero_smul]
      exact hm0 (wcoord_injective (by rw [h5, wcoord_zero]))
    rcases e8W_cone (wcoord (m - (wcoord m i) • Pi.single i 1)) hne hWr with ⟨e, he⟩ | ⟨e, he⟩
    · have heq : m - (wcoord m i) • Pi.single i 1 = fun i => (e i : ℤ) :=
        wcoord_injective he
      have hWe : e8W (wcoord (fun i => (e i : ℤ))) ≠ ⊥ := by
        rw [← he]
        exact hWr
      have hene : e ≠ 0 := by
        intro hz
        rw [hz] at he
        simp only [Pi.zero_apply] at he
        exact hne (by rw [he]; exact wcoord_zero)
      have hcoord : ∀ j : Fin 8, (e j : ℤ)
          = (fun i => (n i : ℤ)) j - (wcoord m i) * (Pi.single i 1 : Fin 8 → ℤ) j := by
        intro j
        have h2 := congrFun heq j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
        have h3 : (e j : ℤ) = m j - (wcoord m i) * (Pi.single i 1 : Fin 8 → ℤ) j := h2.symm
        rw [hm] at h3
        exact h3
      have hsumZ : (∑ j, (e j : ℤ)) = (∑ j, (n j : ℤ)) - wcoord m i := by
        have h1 : (∑ j, (e j : ℤ)) = ∑ j, ((fun i => (n i : ℤ)) j
            - (wcoord m i) * (Pi.single i 1 : Fin 8 → ℤ) j) :=
          Finset.sum_congr rfl fun j _ => hcoord j
        rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
        have h7 : (∑ j : Fin 8, (Pi.single i 1 : Fin 8 → ℤ) j) = 1 := by
          rw [Finset.sum_eq_single i]
          · rw [Pi.single_eq_same]
          · intro b _ hb; rw [Pi.single_eq_of_ne (M := fun _ => ℤ) hb]
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [h7, mul_one]
      have hlt : ∑ i, e i < ∑ i, n i := by
        have h4 : (∑ i, (e i : ℤ)) < (∑ i, (n i : ℤ)) := by
          rw [hsumZ]
          have h3 : 1 ≤ wcoord m i := hi
          omega
        exact_mod_cast h4
      have hnorm := ih (∑ i, e i) (by rw [← hsum]; exact hlt) e rfl hene hWe
      have h1 : e8Nrm (wcoord (fun i => (e i : ℤ))) = e8Nrm (wcoord m) := by
        rw [← heq, e8Nrm_reflect]
      rw [← h1]
      exact hnorm
    · have heq : m - (wcoord m i) • Pi.single i 1 = -(fun i => (e i : ℤ)) :=
        wcoord_injective (by rw [wcoord_neg]; exact he)
      have hoff : ∀ j : Fin 8, j ≠ i → n j = 0 := by
        intro j hj
        have h1 := congrFun heq j
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℤ) hj,
          smul_eq_mul, mul_zero, sub_zero, Pi.neg_apply, Int.cast_neg] at h1
        have h1' : ((n j : ℕ) : ℤ) = -↑(e j) := h1
        have h3 : ((n j : ℕ) : ℤ) ≤ 0 := by rw [h1']; omega
        have h4 : (0 : ℤ) ≤ ((n j : ℕ) : ℤ) := Int.ofNat_nonneg _
        exact_mod_cast (le_antisymm h3 h4)
      have hn_eq : n = n i • Pi.single i 1 := by
        funext j
        by_cases hj : j = i
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        · rw [hoff j hj, Pi.smul_apply, Pi.single_eq_of_ne (M := fun _ => ℕ) hj, smul_eq_mul,
            mul_zero]
      have hni1 : 1 ≤ n i := by
        by_contra hc
        push_neg at hc
        have h0 : n i = 0 := by omega
        exact hn (by rw [hn_eq, h0, zero_smul])
      rcases eq_or_lt_of_le hni1 with h1 | h2
      · have hn1 : n = Pi.single i 1 := by rw [hn_eq, h1.symm, one_smul]
        have hm1 : m = (Pi.single i 1 : Fin 8 → ℤ) := by
          rw [hm, hn1]
          funext j
          by_cases hj : j = i
          · rw [hj]; simp
          · rw [Pi.single_eq_of_ne (M := fun _ => ℕ) hj, Pi.single_eq_of_ne (M := fun _ => ℤ) hj]
            simp
        rw [hm1, e8Nrm_eq_qform,
          show (Pi.single i 1 : Fin 8 → ℤ) = (1 : ℤ) • Pi.single i 1 from (one_smul _ _).symm,
          qform_smul_single]
        norm_num
      · exfalso
        have h2' : 2 ≤ n i := h2
        have hPm : Pm n ≠ ⊥ := by
          intro hbot
          have hWn : W (NWtSum n) ≠ ⊥ := by
            rw [NWtSum_eq_wcoord]
            exact hWm
          have hzero : W (NWtSum n) = ⊥ := by
            rw [Submodule.eq_bot_iff]
            intro x hx
            have hmem : x ∈ (Pm n : Submodule ℂ L8) := by
              rw [Pm]
              exact ⟨e8_W_le_Psub hn hx, hx⟩
            rw [hbot] at hmem
            exact hmem
          exact hWn hzero
        rw [hn_eq] at hPm
        exact hPm (Pm_smul_single_eq_bot (n i) h2' i)
lemma wcoord_reflect (m : Fin 8 → ℤ) (i : Fin 8) :
    wcoord (m - (wcoord m i) • Pi.single i 1)
      = fun j => wcoord m j - wcoord m i * CartanMatrix.E₈ j i := by
  rw [wcoord_sub_smul_single, wcoord_single]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- **Negative part.**  If `n` is a nonzero nonnegative vector such that the weight `-∑ nᵢαᵢ`
occurs in `e₈`, then `-∑ nᵢαᵢ` is a root. -/
theorem e8Nrm_neg_wcoord_of_ne_bot : ∀ N : ℕ, ∀ n : Fin 8 → ℕ, (∑ i, n i) = N → n ≠ 0 →
    e8W (wcoord (-(fun i => (n i : ℤ)))) ≠ ⊥ →
    e8Nrm (wcoord (-(fun i => (n i : ℤ)))) = 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n hsum hn hW
    set m : Fin 8 → ℤ := fun i => (n i : ℤ) with hm
    have hm0 : m ≠ 0 := by
      intro hz
      refine hn ?_
      funext i
      simp only [Pi.zero_apply]
      have h1 := congrFun hz i
      have h1' : ((n i : ℕ) : ℤ) = 0 := h1
      omega
    have hWm : e8W (wcoord (-m)) ≠ ⊥ := by
      simpa [wcoord_neg] using hW
    have hγ0 : wcoord (-m) ≠ 0 := by
      rw [wcoord_neg]
      intro hz
      refine hm0 (wcoord_injective ?_)
      rw [wcoord_zero]
      exact neg_eq_zero.mp hz
    obtain ⟨i, hi⟩ : ∃ i, wcoord (-m) i ≤ -1 := by
      have hpos : 0 < ∑ j, (n j : ℚ) * (wcoord m j : ℚ) := by
        have h1 : (∑ j, (n j : ℚ) * (wcoord m j : ℚ)) = qform m := by
          rw [qform, qpair_eq]
          exact Finset.sum_congr rfl fun j _ => rfl
        rw [h1]
        exact qform_pos hm0
      by_contra hc
      push_neg at hc
      have hle : ∑ j, (n j : ℚ) * (wcoord m j : ℚ) ≤ 0 :=
        Finset.sum_nonpos fun j _ => by
          have h2 : (0 : ℚ) ≤ (wcoord (-m) j : ℚ) := by exact_mod_cast hc j
          have h5 : (wcoord (-m) j : ℚ) = -(wcoord m j : ℚ) := by
            rw [wcoord_neg]
            simp
          have h3 : (wcoord m j : ℚ) ≤ 0 := by linarith
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h3
      linarith
    have hreflect : wcoord (-m - (wcoord (-m) i) • Pi.single i 1)
        = fun j => wcoord (-m) j - wcoord (-m) i * CartanMatrix.E₈ j i :=
      wcoord_reflect (-m) i
    have hWr : e8W (wcoord (-m - (wcoord (-m) i) • Pi.single i 1)) ≠ ⊥ :=
      hreflect ▸ e8W_reflect_ne_bot' i (wcoord (-m)) hWm
    have hne : wcoord (-m - (wcoord (-m) i) • Pi.single i 1) ≠ 0 := by
      intro hz
      have h1 : wcoord (-m) = (wcoord (-m) i) • wcoord (Pi.single i 1) := by
        have h2 := wcoord_sub_smul_single (-m) i
        rw [h2] at hz
        exact sub_eq_zero.mp hz
      have h3 : wcoord (-m) i = 0 := by
        have h4 := congrFun h1 i
        rw [wcoord_single] at h4
        simp only [Pi.smul_apply, smul_eq_mul] at h4
        rw [show CartanMatrix.E₈ i i = 2 from E8_diag i] at h4
        omega
      exact hγ0 (by rw [h1, h3, zero_smul])
    rcases e8W_cone (wcoord (-m - (wcoord (-m) i) • Pi.single i 1)) hne hWr with ⟨e, he⟩ | ⟨e, he⟩
    · -- the reflection is a nonnegative weight
      have hWe : e8W (wcoord (fun i => (e i : ℤ))) ≠ ⊥ := by
        rw [← he]
        exact hWr
      have hene : e ≠ 0 := by
        intro hz
        rw [hz] at he
        simp only [Pi.zero_apply] at he
        exact hne (by rw [he]; funext j; simp [wcoord])
      have hpos := e8Nrm_wcoord_of_ne_bot (∑ i, e i) e rfl hene hWe
      have h1 : e8Nrm (wcoord (-m)) = e8Nrm (wcoord (fun i => (e i : ℤ))) := by
        have h2 : wcoord (fun i => (e i : ℤ)) = wcoord (-m - (wcoord (-m) i) • Pi.single i 1) :=
          he.symm
        rw [h2, e8Nrm_reflect i (-m)]
      rw [h1]
      exact hpos
    · -- the reflection is a nonpositive weight: induction
      have heq : -m - (wcoord (-m) i) • Pi.single i 1 = -(fun i => (e i : ℤ)) := by
        refine wcoord_injective ?_
        have h1 : wcoord (-(fun i => (e i : ℤ))) = -wcoord (fun i => (e i : ℤ)) :=
          wcoord_neg (fun i => (e i : ℤ))
        rw [h1]
        exact he
      have he0 : e ≠ 0 := by
        intro hz
        rw [hz] at he
        simp only [Pi.zero_apply] at he
        exact hne (by rw [he]; funext j; simp [wcoord])
      have hlt : ∑ i, e i < ∑ i, n i := by
        have hcoord : ∀ j : Fin 8, (e j : ℤ) = ((fun i => (n i : ℤ)) j
            + (wcoord (-m) i) * (Pi.single i 1 : Fin 8 → ℤ) j) := by
          intro j
          have h2 := congrFun heq j
          rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h2
          have hmj : m j = ((fun i => (n i : ℤ)) j) := by rw [hm]
          simp only [hmj, Pi.neg_apply] at h2
          linarith
        have hsumZ : (∑ j, (e j : ℤ)) = (∑ j, (n j : ℤ)) + wcoord (-m) i := by
          have h1 : (∑ j, (e j : ℤ)) = ∑ j, ((fun i => (n i : ℤ)) j
              + (wcoord (-m) i) * (Pi.single i 1 : Fin 8 → ℤ) j) :=
            Finset.sum_congr rfl fun j _ => hcoord j
          rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
          have h7 : (∑ j : Fin 8, (Pi.single i 1 : Fin 8 → ℤ) j) = 1 := by
            rw [Finset.sum_eq_single i]
            · rw [Pi.single_eq_same]
            · intro b _ hb; rw [Pi.single_eq_of_ne (M := fun _ => ℤ) hb]
            · intro h; exact absurd (Finset.mem_univ i) h
          rw [h7, mul_one]
        have h4 : (∑ i, (e i : ℤ)) < (∑ i, (n i : ℤ)) := by
          rw [hsumZ]
          have h3 : wcoord (-m) i ≤ -1 := hi
          omega
        exact_mod_cast h4
      have he' : wcoord (-(fun i => (e i : ℤ))) = wcoord (-m - (wcoord (-m) i) • Pi.single i 1) := by
        have h1 : wcoord (-(fun i => (e i : ℤ))) = -wcoord (fun i => (e i : ℤ)) := wcoord_neg _
        rw [h1, ← he]
      have hWe : e8W (wcoord (-(fun i => (e i : ℤ)))) ≠ ⊥ := by
        rw [he']
        exact hWr
      have hnorm := ih (∑ i, e i) (by rw [← hsum]; exact hlt) e rfl he0 hWe
      have h2 : e8Nrm (wcoord (-m)) = e8Nrm (wcoord (-(fun i => (e i : ℤ)))) := by
        rw [he', e8Nrm_reflect i (-m)]
      rw [h2]
      exact hnorm
/-- **Support bound.**  A nonzero integral weight which is not a root has zero weight space. -/
theorem e8W_eq_bot_of_not_root (μ : Fin 8 → ℤ) (hμ : μ ≠ 0) (hnrm : e8Nrm μ ≠ 2) :
    e8W μ = ⊥ := by
  by_contra hcon
  rcases e8W_cone μ hμ hcon with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hn0 : n ≠ 0 := by
      intro h0
      refine hμ ?_
      rw [hn, h0]
      funext j
      simp [wcoord]
    have hWe : e8W (wcoord (fun i => (n i : ℤ))) ≠ ⊥ := by
      rw [← hn]
      exact hcon
    have h2 := e8Nrm_wcoord_of_ne_bot (∑ i, n i) n rfl hn0 hWe
    exact hnrm (by rw [hn]; exact h2)
  · have hn0 : n ≠ 0 := by
      intro h0
      refine hμ ?_
      rw [hn, h0]
      funext j
      simp [wcoord]
    have hWe : e8W (wcoord (-(fun i => (n i : ℤ)))) ≠ ⊥ := by
      rw [wcoord_neg, ← hn]
      exact hcon
    have h2 := e8Nrm_neg_wcoord_of_ne_bot (∑ i, n i) n rfl hn0 hWe
    exact hnrm (by rw [hn]; simpa [wcoord_neg] using h2)
-- ----------------------------------------------------------------------------
-- The weight spaces are independent and span `e₈`, and each has the expected dimension

/-- The operators `ad (H i)` commute, because the `H i` commute (Serre relation `HH`). -/
lemma ad_SerreH_commute (i j : Fin 8) :
    LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH i) * LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH j)
      = LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH j) * LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH i) := by
  have h : ⁅LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH i),
      LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH j)⁆ = 0 := by
    rw [← LieHom.map_lie (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)) (SerreH i) (SerreH j),
      serreLie_HH, map_zero]
  rw [Ring.lie_def, sub_eq_zero] at h
  exact h

/-- Weight spaces of distinct weights are independent. -/
lemma e8W_iSupIndep : iSupIndep e8W := by
  refine Commons.LinearAlgebra.Eigenspace.iSupIndep_eigenspace_of_commute_of_torsionfree
    (R := ℂ) (M := LieAlgebra.e₈ ℂ) (ι := Fin 8) (κ := Fin 8 → ℤ)
    (T := fun i => LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH i))
    (χ := fun (μ : Fin 8 → ℤ) (i : Fin 8) => (μ i : ℂ)) ?_ ?_
  · intro i j; exact ad_SerreH_commute i j
  · intro μ ν h
    by_contra hcon
    push Not at hcon
    exact h (funext fun i => by exact_mod_cast hcon i)




lemma e8W_iSup_eq_top : (⨆ μ : Fin 8 → ℤ, e8W μ) = ⊤ := by
  rw [show (fun μ : Fin 8 → ℤ => e8W μ)
      = (fun μ : Fin 8 → ℤ => W (fun i => (μ i : ℂ))) from rfl]
  exact e8_weightSpace_iSup_eq_top

/-- Rewrite a sum over the subtype `↥T` as a sum over the finset `T`. -/
lemma rank_sum_subtype_eq_sum_finset (T : Finset (Fin 8 → ℤ)) :
    (∑ μ : ↥T, Module.rank ℂ ↥(e8W (μ : Fin 8 → ℤ)))
      = ∑ μ ∈ T, Module.rank ℂ ↥(e8W μ) := by
  rw [← Finset.sum_attach (s := T) (f := fun μ : Fin 8 → ℤ => Module.rank ℂ ↥(e8W μ)),
    Finset.attach_eq_univ]

theorem e8_finrank : Module.finrank ℂ (LieAlgebra.e₈ ℂ) = 248 := by
  classical
  have h_support : ∀ μ : Fin 8 → ℤ, μ ≠ 0 → e8Nrm μ ≠ 2 → e8W μ = ⊥ := e8W_eq_bot_of_not_root
  have h_rootdim : ∀ μ : Fin 8 → ℤ, μ ≠ 0 → e8Nrm μ = 2 → Module.finrank ℂ ↥(e8W μ) = 1 := by
    intro μ hne h2
    exact e8_root_weightSpace_finrank_eq_one μ hne h2
  have h_zerodim : Module.finrank ℂ ↥(e8W 0) = 8 := by
    have h : e8W 0 = ⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
        (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
          (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (0 : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ)) := by
      simp only [e8W, wtSpace, Pi.zero_apply, Int.cast_zero]
    rw [h]
    exact e8_zero_weightSpace_finrank
  obtain ⟨rt, hrt_mem, hrt_card⟩ := exists_finset_e8_roots
  set T : Finset (Fin 8 → ℤ) := insert 0 rt with hT
  have h0rt : (0 : Fin 8 → ℤ) ∉ rt := by
    intro h; exact ((hrt_mem 0).mp h).1 rfl
  have hsupp : ∀ μ : Fin 8 → ℤ, μ ∉ T → e8W μ = ⊥ := by
    intro μ hμ
    have hne : μ ≠ 0 := by rintro rfl; exact hμ (by rw [hT]; exact Finset.mem_insert_self _ _)
    have hnr : e8Nrm μ ≠ 2 := by
      intro h2
      exact hμ (by rw [hT]; exact Finset.mem_insert_of_mem ((hrt_mem μ).mpr ⟨hne, h2⟩))
    exact h_support μ hne hnr
  have hspan : (⨆ μ : ↥T, e8W (μ : Fin 8 → ℤ)) = ⊤ := by
    rw [eq_top_iff, ← e8W_iSup_eq_top]
    refine iSup_le (fun μ => ?_)
    by_cases h : μ ∈ T
    · exact le_iSup (fun ν : ↥T => e8W (ν : Fin 8 → ℤ)) ⟨μ, h⟩
    · rw [hsupp μ h]; exact bot_le
  have hind : iSupIndep (fun μ : ↥T => e8W (μ : Fin 8 → ℤ)) := by
    refine Commons.LinearAlgebra.Eigenspace.iSupIndep_eigenspace_of_commute_of_torsionfree
      (R := ℂ) (M := LieAlgebra.e₈ ℂ) (ι := Fin 8) (κ := ↥T)
      (T := fun i => LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ) (SerreH i))
      (χ := fun (μ : ↥T) (i : Fin 8) => (((μ : Fin 8 → ℤ)) i : ℂ)) ?_ ?_
    · intro i j; exact ad_SerreH_commute i j
    · intro μ ν h
      by_contra hcon
      push Not at hcon
      exact h (Subtype.ext (funext fun i => by exact_mod_cast hcon i))
  have hrank0 : Module.rank ℂ ↥(e8W 0) = 8 :=
    (Module.rank_eq_ofNat_iff_finrank_eq_ofNat 8).mpr h_zerodim
  have hrankroot : ∀ μ ∈ rt, Module.rank ℂ ↥(e8W μ) = 1 := by
    intro μ hμ
    obtain ⟨hne, h2⟩ := (hrt_mem μ).mp hμ
    exact Module.rank_eq_one_iff_finrank_eq_one.mpr (h_rootdim μ hne h2)
  have h_ranksum : Module.rank ℂ (LieAlgebra.e₈ ℂ)
      = ∑ μ : ↥T, Module.rank ℂ ↥(e8W (μ : Fin 8 → ℤ)) := by
    have h1 := Commons.LinearAlgebra.Submodule.rank_iSup_eq_sum_of_iSupIndep
      (f := fun μ : ↥T => e8W (μ : Fin 8 → ℤ)) hind
    rw [hspan] at h1
    rw [← h1]
    exact (Submodule.topEquiv (R := ℂ) (M := LieAlgebra.e₈ ℂ)).rank_eq.symm
  have hrank : Module.rank ℂ (LieAlgebra.e₈ ℂ) = (248 : Cardinal) := by
    rw [h_ranksum]
    rw [rank_sum_subtype_eq_sum_finset T]
    rw [hT, Finset.sum_insert h0rt]
    rw [hrank0, Finset.sum_congr rfl (fun μ hμ => hrankroot μ hμ), Finset.sum_const, hrt_card]
    norm_num
  exact Module.finrank_eq_of_rank_eq hrank

end Commons.Algebra.Lie
