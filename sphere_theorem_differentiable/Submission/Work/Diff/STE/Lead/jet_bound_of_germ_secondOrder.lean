import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.Gal.gardLeibnizLocal
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.Lead.pdList_add_cm
import Submission.Work.Diff.STE.Lead.exists_contDiff_eventuallyEq_of_contDiffAt
import Submission.Work.Diff.STE.Lead.pdVec_sum2_mul_le
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Jet bounds from a germ identity of order two

The target `Work.Diff.STE.Lead.jet_bound_of_germ_secondOrder` is the *local Leibniz bound of second
order*: if `F` agrees, near a point `z`, with the second order operator

`y ↦ ∑_{c d} A c d y · ∂_c ∂_d G y + Ψ y`

applied to a function `G`, and the jets of `A c d` (up to order `N`), of `∂_c∂_d G` (up to order
`N`) and of `Ψ` (up to order `N`) are bounded at `z` by `CA`, `CD` and `CR`, then all the jets of
`F` up to order `N` at `z` are bounded by `C (CA·CD + CR + 1)`, with `C` depending only on `n` and
`N`.

## Route

1. `pdVec_congr_germ`: the iterated partial derivatives at a point only depend on the germ (this is
   `Filter.EventuallyEq.fderiv` iterated, and it needs no differentiability hypothesis at all,
   because `fderiv` is a germ-local operation defined everywhere).  Hence we may replace `F` by the
   sum `T + Ψ` and `Ψ` by any function equal to it near `z`.

2. `pdVec_sum2_mul_le` (delegated): the jets of `T = ∑_c ∑_d A c d · ∂_c∂_d G` at `z` are bounded
   by `n² · (2^N (n+1)^N (N+1)) · (CA·CD)`: the iterated partial derivatives distribute over the
   finite double sum and the iterated Leibniz rule (Mathlib's `norm_iteratedFDeriv_mul_le`, via
   `pdVec_mul_le`) bounds each product by its two jet bounds; the hypotheses bound *all* orders
   `≤ N`, so every term of the Leibniz expansion is `≤ CA·CD` and the sharp constant is `2^N`.

3. `exists_contDiff_eventuallyEq_of_contDiffAt` (delegated): a function which is `C^{N+1}` at `z`
   agrees near `z` with a globally `C^{N+1}` function `Ψ'` (multiply by a bump).  Note that only a
   *finite* order can be globalised (`ContDiffAt ℝ ∞` does not imply `C^∞` on a fixed
   neighbourhood), which is the reason the two estimates below are carried at the finite order
   `N + 1`.

4. `pdList_add_cm` (delegated): additivity of the iterated partial derivatives of a sum, at finite
   order: `∂^L (f + g) = ∂^L f + ∂^L g` whenever `|L| + 1 ≤ M` and `f, g` are `C^M` globally.  It is
   applied to `T + Ψ'` (both globally `C^{N+1}`), and combined with the germ congruence to get
   `∂^β F z = ∂^β T z + ∂^β Ψ z`.

5. The arithmetic: `n² K (CA·CD) + CR ≤ (n² K + 1)(CA·CD + CR + 1)`.
-/

namespace Work.Diff.STE.Lead

/-- The iterated partial derivatives at a point depend only on the germ at that point. -/
lemma pdVec_congr_germ {n m : ℕ} {z : Fin n → ℝ} {f g : (Fin n → ℝ) → ℂ}
    (h : f =ᶠ[nhds z] g) (β : Fin m → Fin n) :
    Work.Diff.STE.pdVec m β f z = Work.Diff.STE.pdVec m β g z := by
  have key : ∀ l : List (Fin n),
      Work.Diff.STE.pdList l f =ᶠ[nhds z] Work.Diff.STE.pdList l g := by
    intro l
    induction l with
    | nil => simpa only [Work.Diff.STE.pdList, List.foldr_nil] using h
    | cons i t ih =>
        have h2 : Work.Diff.STE.pd i (Work.Diff.STE.pdList t f) =ᶠ[nhds z]
            Work.Diff.STE.pd i (Work.Diff.STE.pdList t g) := by
          filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
          simp only [Work.Diff.STE.pd, hy]
        simpa only [Work.Diff.STE.pdList, List.foldr_cons] using h2
  rw [Work.Diff.STE.pdVec]
  exact (key (List.ofFn β)).eq_of_nhds

theorem jet_bound_of_germ_secondOrder {n N : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F G Ψ : (Fin n → ℝ) → ℂ)
        (A : Fin n → Fin n → (Fin n → ℝ) → ℂ) (z : Fin n → ℝ)
        (CA KG CR CD : ℝ), 0 ≤ CA → 0 ≤ KG → 0 ≤ CR → 0 ≤ CD →
        (∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d)) →
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) G →
        ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) Ψ z →
        F =ᶠ[nhds z] ((fun y : Fin n → ℝ =>
            ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) + Ψ) →
        (∀ (c d : Fin n) (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β (A c d) z‖ ≤ CA) →
        (∀ (m : ℕ), m ≤ N + 2 → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β G z‖ ≤ KG) →
        (∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β Ψ z‖ ≤ CR) →
        (∀ (c d : Fin n) (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β (Work.Diff.STE.pd c (Work.Diff.STE.pd d G)) z‖ ≤ CD) →
        ∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β F z‖ ≤ C * (CA * CD + CR + 1) := by
  classical
  refine ⟨(n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) + 1,
    by positivity, ?_⟩
  intro F G Ψ A z CA KG CR CD hCA hKG hCR hCD hAsm hGsm hΨsm hgerm hAj hGj hΨj hDj m hm β
  set T : (Fin n → ℝ) → ℂ :=
    fun y => ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y with hT
  -- smoothness of the summand factors
  have hpd : ∀ c d : Fin n,
      ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd c (Work.Diff.STE.pd d G)) :=
    fun c d => Work.Diff.STE.flat.contDiff_pd_top
      (Work.Diff.STE.flat.contDiff_pd_top hGsm d) c
  have hTsm : ContDiff ℝ (⊤ : ℕ∞) T := by
    rw [hT]
    exact ContDiff.sum (fun c _ => ContDiff.sum (fun d _ => (hAsm c d).mul (hpd c d)))
  have hle : (((N + 1 : ℕ)) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    by exact_mod_cast (le_top : (((N + 1 : ℕ)) : ℕ∞) ≤ ⊤)
  have hTle : ContDiff ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) T := hTsm.of_le hle
  -- globalisation of `Ψ`
  have hΨK : ContDiffAt ℝ (((N + 1 : ℕ)) : WithTop ℕ∞) Ψ z := hΨsm.of_le hle
  obtain ⟨Ψ', hΨ'sm, hΨ'eq⟩ := exists_contDiff_eventuallyEq_of_contDiffAt (K := N + 1) hΨK
  -- additivity at order `N`
  have hadd := pdList_add_cm (List.ofFn β) (by rw [List.length_ofFn]; exact hm)
    (f := T) (g := Ψ') hTle hΨ'sm
  have hval : Work.Diff.STE.pdVec m β (T + Ψ') z
      = Work.Diff.STE.pdVec m β T z + Work.Diff.STE.pdVec m β Ψ' z := by
    have h := congrFun hadd z
    simpa only [Work.Diff.STE.pdVec, Pi.add_apply] using h
  -- the bound on the leading part
  have hTbound : ‖Work.Diff.STE.pdVec m β T z‖
      ≤ (n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (CA * CD) := by
    have h := pdVec_sum2_mul_le (n := n) (N := N) (z := z) (A := A) (G := G)
      (CA := CA) (CD := CD) hCA hCD hAsm hGsm hAj hDj m hm β
    rw [hT]
    exact h
  -- the bound on the `Ψ` part
  have hΨbound : ‖Work.Diff.STE.pdVec m β Ψ' z‖ ≤ CR := by
    rw [pdVec_congr_germ hΨ'eq β]
    exact hΨj m hm β
  -- transfer from `F` to the sum
  have hFcongr : Work.Diff.STE.pdVec m β F z = Work.Diff.STE.pdVec m β (T + Ψ) z := by
    have h : F =ᶠ[nhds z] ((fun y : Fin n → ℝ =>
        ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) + Ψ) := hgerm
    rw [hT]
    exact pdVec_congr_germ h β
  have hcongr2 : Work.Diff.STE.pdVec m β (T + Ψ) z
      = Work.Diff.STE.pdVec m β (T + Ψ') z :=
    pdVec_congr_germ
      (Filter.EventuallyEq.add (Filter.EventuallyEq.refl (nhds z) T) hΨ'eq.symm) β
  have hX0 : 0 ≤ CA * CD := mul_nonneg hCA hCD
  have hM0 : 0 ≤ (n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) := by
    positivity
  calc ‖Work.Diff.STE.pdVec m β F z‖
      = ‖Work.Diff.STE.pdVec m β (T + Ψ) z‖ := by rw [hFcongr]
    _ = ‖Work.Diff.STE.pdVec m β (T + Ψ') z‖ := by rw [hcongr2]
    _ = ‖Work.Diff.STE.pdVec m β T z + Work.Diff.STE.pdVec m β Ψ' z‖ := by rw [hval]
    _ ≤ ‖Work.Diff.STE.pdVec m β T z‖ + ‖Work.Diff.STE.pdVec m β Ψ' z‖ := norm_add_le _ _
    _ ≤ (n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (CA * CD) + CR :=
        add_le_add hTbound hΨbound
    _ ≤ ((n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) + 1)
          * (CA * CD + CR + 1) := by
        nlinarith [hX0, hM0, hCR]

end Work.Diff.STE.Lead
