import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDBasic.finite_sets

/-!
# Per-vector attainment of the successive minima `lam L 1, …, lam L j`

For a sublattice `L ⊆ ℤ^5` and `j ≤ rk L` we produce `j` linearly independent vectors
`f 0, …, f (j-1)` of `L` with `‖f i‖ ≤ lam L (i.val + 1)`, i.e. with the `i`-th vector
respecting the `(i+1)`-st successive minimum.

Two ingredients:

* `lamAttained_aux` : the `i`-th successive minimum `lam L i` is *attained* — there are
  `i` linearly independent vectors of `L` of norm at most `lam L i`.  (It is an infimum
  over radii, and the lattice points in a ball are finite, so the infimum is a minimum.)
* `lamAttained_snoc` : given `k` independent vectors `f` and `k+1` independent vectors `g`,
  some `g t` can be appended to `f`.  (Pass to `ℚ^5`, where the dimension count
  `dim span g = k+1 > k = dim span f` applies.)

These are assembled by an induction on `j`, appending one vector at a time to reach the
`(i+1)`-st successive minimum.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Finset

namespace Work.HP.Q44Child

/-! ## Attainment of the successive minima -/

/-- For `i ≤ rk L` the `i`-th successive minimum is attained: there are `i` linearly
independent lattice vectors of `L` all of norm at most `lam L i`. -/
theorem lamAttained_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ))
    {i : ℕ} (hi : i ≤ Work.HP.rk L) :
    ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ j, Work.HP.eNorm (f j) ≤ Work.HP.lam L i := by
  classical
  by_cases hi0 : i = 0
  · subst hi0
    exact ⟨fun j => j.elim0, fun j => j.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  · have hi1 : 0 < i := Nat.pos_of_ne_zero hi0
    obtain ⟨g₀, hg₀L, hg₀I, hg₀b⟩ :=
      Work.HP.lam_witness L hi (ρ := Work.HP.lam L i + 1) (by linarith)
    let T : Set (Fin i → (ι → ℤ)) :=
      {f | (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧
        ∀ j, Work.HP.eNorm (f j) ≤ Work.HP.lam L i + 1}
    let M : (Fin i → (ι → ℤ)) → ℝ :=
      fun f => Finset.univ.sup' ⟨⟨0, hi1⟩, Finset.mem_univ _⟩ fun j => Work.HP.eNorm (f j)
    have hTfin : T.Finite := by
      refine (Set.Finite.pi (fun _ => Work.HP.MDBasic.finite_eNorm_le (Work.HP.lam L i + 1))).subset ?_
      intro f hf
      rw [Set.mem_pi]
      intro j _
      exact hf.2.2 j
    have hTne : T.Nonempty := ⟨g₀, hg₀L, hg₀I, hg₀b⟩
    obtain ⟨t₀, ht₀T, ht₀min⟩ := Set.exists_min_image T M hTfin hTne
    have hMle : M t₀ ≤ Work.HP.lam L i + 1 := Finset.sup'_le _ _ fun j _ => ht₀T.2.2 j
    have hbound : M t₀ ≤ Work.HP.lam L i := by
      by_contra hc
      push Not at hc
      have hrhoM : (Work.HP.lam L i + M t₀) / 2 < M t₀ := by linarith
      have hlamrho : Work.HP.lam L i < (Work.HP.lam L i + M t₀) / 2 := by linarith
      obtain ⟨h, hhL, hhI, hhb⟩ :=
        Work.HP.lam_witness L hi (ρ := (Work.HP.lam L i + M t₀) / 2) hlamrho
      have hhT : h ∈ T := ⟨hhL, hhI, fun j => le_of_lt ((hhb j).trans_lt (hrhoM.trans_le hMle))⟩
      have hlt : M h < M t₀ := lt_of_le_of_lt (Finset.sup'_le _ _ fun j _ => hhb j) hrhoM
      exact absurd (ht₀min h hhT) (not_le.mpr hlt)
    exact ⟨t₀, ht₀T.1, ht₀T.2.1,
      fun j => (Finset.le_sup' (fun j => Work.HP.eNorm (t₀ j)) (Finset.mem_univ j)).trans hbound⟩

/-! ## Transfer of linear independence from `ℤ^ι` to `ℚ^ι` -/

/-- The coefficientwise map `ℤ^ι → ℚ^ι`, as a `ℤ`-linear map. -/
def lamAttained_toRatLM (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) where
  toFun v := fun i => (v i : ℚ)
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp [Pi.smul_apply]

lemma lamAttained_toRatLM_injective (ι : Type*) [Fintype ι] :
    Function.Injective (lamAttained_toRatLM ι) := by
  intro v w h
  funext i
  exact_mod_cast (show ((v i : ℤ) : ℚ) = ((w i : ℤ) : ℚ) from congrFun h i)

/-- A family of integer vectors is linearly independent over `ℤ` if and only if its
coefficientwise image in `ℚ^ι` is linearly independent over `ℚ`. -/
theorem lamAttained_linIndep_iff {ι : Type*} [Fintype ι] {n : ℕ} (f : Fin n → (ι → ℤ)) :
    LinearIndependent ℤ f ↔ LinearIndependent ℚ (fun j => fun i => (f j i : ℚ)) := by
  constructor
  · intro h
    have h2 : LinearIndependent ℤ (fun j => lamAttained_toRatLM ι (f j)) :=
      h.map' (lamAttained_toRatLM ι) (by rw [LinearMap.ker_eq_bot]; exact lamAttained_toRatLM_injective ι)
    exact h2.localization ℚ (nonZeroDivisors ℤ)
  · intro h
    rw [Fintype.linearIndependent_iff] at h ⊢
    intro g hg
    have hQ : (∑ j, ((g j : ℚ)) • (fun i => (f j i : ℚ))) = 0 := by
      funext i
      have hgi : (∑ j, g j * f j i) = 0 := by
        have h1 := congrFun hg i
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h1
      calc (∑ j, ((g j : ℚ)) • (fun i => (f j i : ℚ))) i
          = ∑ j, (g j : ℚ) * (f j i : ℚ) := by simp [Pi.smul_apply, Finset.sum_apply]
        _ = ((∑ j, g j * f j i : ℤ) : ℚ) := by push_cast; ring
        _ = 0 := by rw [hgi]; rfl
    intro j
    have hgj : ((g j : ℤ) : ℚ) = 0 := h (fun j => ((g j : ℤ) : ℚ)) hQ j
    exact_mod_cast hgj

/-- Given `k` linearly independent integer vectors `f` and `k+1` linearly independent
integer vectors `g`, one of the `g t` extends `f` to an independent family. -/
theorem lamAttained_snoc {ι : Type*} [Fintype ι] {k : ℕ} {f : Fin k → (ι → ℤ)}
    {g : Fin (k + 1) → (ι → ℤ)} (hf : LinearIndependent ℤ f) (hg : LinearIndependent ℤ g) :
    ∃ t : Fin (k + 1), LinearIndependent ℤ (Fin.snoc f (g t)) := by
  classical
  have hfQ : LinearIndependent ℚ (fun j => fun i => (f j i : ℚ)) := (lamAttained_linIndep_iff f).mp hf
  have hgQ : LinearIndependent ℚ (fun j => fun i => (g j i : ℚ)) := (lamAttained_linIndep_iff g).mp hg
  let U : Submodule ℚ (ι → ℚ) := Submodule.span ℚ (Set.range fun j => fun i => (f j i : ℚ))
  let W : Submodule ℚ (ι → ℚ) := Submodule.span ℚ (Set.range fun j => fun i => (g j i : ℚ))
  have hUr : Module.finrank ℚ U = k := by simpa [U] using finrank_span_eq_card hfQ
  have hWr : Module.finrank ℚ W = k + 1 := by simpa [W] using finrank_span_eq_card hgQ
  have hnotle : ¬ W ≤ U := by
    intro hle
    have hfin := Submodule.finrank_mono hle
    rw [hWr, hUr] at hfin
    omega
  have hex : ∃ t : Fin (k + 1), (fun i => (g t i : ℚ)) ∉ U := by
    by_contra hc
    push Not at hc
    exact hnotle (Submodule.span_le.mpr (fun x hx => by
      rw [Set.mem_range] at hx
      obtain ⟨t, rfl⟩ := hx
      exact hc t))
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ?_⟩
  let F' : Fin (k + 1) → (ι → ℤ) := Fin.snoc f (g t)
  have hQsnoc : LinearIndependent ℚ
      (Fin.snoc (fun j => fun i => (f j i : ℚ)) (fun i => (g t i : ℚ))) :=
    LinearIndependent.finSnoc hfQ ht
  have heq : Fin.snoc (fun j => fun i => (f j i : ℚ)) (fun i => (g t i : ℚ))
      = fun j => fun i => (F' j i : ℚ) := by
    funext j i
    rcases Fin.eq_castSucc_or_eq_last j with ⟨m, rfl⟩ | rfl <;> simp [F']
  rw [heq] at hQsnoc
  exact (lamAttained_linIndep_iff F').mpr hQsnoc

/-! ## The target -/

theorem lam_attained (L : Submodule ℤ (Fin 5 → ℤ)) (j : ℕ) (hj : 0 < j) (hj' : j ≤ Work.HP.rk L) :
    ∃ f : Fin j → (Fin 5 → ℤ), (∀ i, f i ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ i, Work.HP.eNorm (f i) ≤ Work.HP.lam L (i.val + 1) := by
  have key : ∀ m : ℕ, m ≤ j → ∃ f : Fin m → (Fin 5 → ℤ), (∀ i, f i ∈ L) ∧ LinearIndependent ℤ f ∧
      ∀ i, Work.HP.eNorm (f i) ≤ Work.HP.lam L (i.val + 1) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun i => i.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfI, hfb⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨g, hgL, hgI, hgb⟩ := lamAttained_aux (i := k + 1) L (le_trans hk hj')
      obtain ⟨t, ht⟩ := lamAttained_snoc hfI hgI
      refine ⟨Fin.snoc f (g t), ?_, ht, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨m, rfl⟩ | rfl
        · simpa using hfL m
        · simpa using hgL t
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨m, rfl⟩ | rfl
        · simpa using hfb m
        · simpa using hgb t
  exact key j le_rfl

end Work.HP.Q44Child
