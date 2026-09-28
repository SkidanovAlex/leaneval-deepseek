import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.lam_basic
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.Lat.detLAux

set_option maxHeartbeats 1000000

namespace Work.HP.MDEstimates

open Work.HP

/-!
# `Work.HP.MDEstimates.hypLatCount`

Number of primitive rank-3 sublattices of `ℤ^5` lying in a fixed hyperplane `a^⊥` (`a ≠ 0`)
with successive minima bounded by `s`, uniformly in `a`.

The proof reduces the count to a count of primitive rank-3 sublattices of `ℤ^4` by dropping a
coordinate `i₀` with `a i₀ ≠ 0`: the coordinate projection `dropICoord i₀` is injective on
`latOrth a`, and `L ↦ satLat (L.map (dropICoord i₀))` is an injection of the hyperplane lattices
into the `ℤ^4` lattices that does not increase the successive minima.  The `ℤ^4` count is then
bounded with the paper's "number of lattices" theorem `Work.HP.Sig2.num_lattices_of`, fed with
Minkowski's second theorem `Work.HP.Sig2.minkowski_prod`.
-/

/-- Coordinate projection `ℤ^5 → ℤ^{{j // j ≠ i₀}}` dropping the `i₀`-th coordinate. -/
def dropICoord (i₀ : Fin 5) : (Fin 5 → ℤ) →ₗ[ℤ] ({j : Fin 5 // j ≠ i₀} → ℤ) where
  toFun x := fun j => x j.1
  map_add' x y := by funext j; rfl
  map_smul' c x := by funext j; rfl

lemma dropICoord_apply (i₀ : Fin 5) (x : Fin 5 → ℤ) (j : {j : Fin 5 // j ≠ i₀}) :
    dropICoord i₀ x j = x j.1 := rfl

/-- The coordinate projection is injective on the hyperplane `a^⊥` when `a i₀ ≠ 0`. -/
lemma dropICoord_injective_on_latOrth (a : Fin 5 → ℤ) (i₀ : Fin 5) (hai : a i₀ ≠ 0)
    {x y : Fin 5 → ℤ} (hx : x ∈ latOrth a) (hy : y ∈ latOrth a)
    (h : dropICoord i₀ x = dropICoord i₀ y) : x = y := by
  have hd : x - y ∈ latOrth a := Submodule.sub_mem _ hx hy
  rw [Work.HP.mem_latOrth] at hd
  have hcoord : ∀ j : Fin 5, j ≠ i₀ → x j = y j := by
    intro j hj
    have := congrFun h ⟨j, hj⟩
    simpa [dropICoord] using this
  have hsum : dotZ (x - y) a = 0 := hd
  rw [dotZ] at hsum
  have hsplit : ∑ i, (x - y) i * a i = (x i₀ - y i₀) * a i₀ := by
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; have := hcoord j hj; simp [Pi.sub_apply, this]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [hsplit] at hsum
  have hx0 : x i₀ = y i₀ := by
    rcases mul_eq_zero.mp hsum with h3 | h3
    · linarith
    · exact absurd h3 hai
  funext j
  by_cases hj : j = i₀
  · subst hj; exact hx0
  · exact hcoord j hj

/-- Lattice vectors of the hyperplane `a^⊥`, with the `dotZ`-pairing. -/
lemma le_latOrth_of_dotZ (a : Fin 5 → ℤ) {L : Submodule ℤ (Fin 5 → ℤ)}
    (h : ∀ x ∈ L, dotZ x a = 0) : L ≤ latOrth a := by
  intro x hx
  rw [Work.HP.mem_latOrth]
  exact h x hx

/-- The successive minima are antitone for inclusions of lattices, on indices up to the rank. -/
lemma lam_antitone_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Submodule ℤ (ι → ℤ)} (h : M ≤ N) {i : ℕ} (hi : i ≤ rk M) : lam N i ≤ lam M i := by
  rw [Work.HP.lam_eq_sInf, Work.HP.lam_eq_sInf]
  refine csInf_le_csInf (Work.HP.bddBelow_lamSet N i) (Work.HP.lamSet_nonempty M hi) ?_
  intro r hr
  obtain ⟨hr0, f, hfL, hfI, hfr⟩ := hr
  exact ⟨hr0, f, fun j => h (hfL j), hfI, hfr⟩

/-- The Euclidean norm does not increase under dropping a coordinate. -/
lemma eNorm_dropICoord_le (i₀ : Fin 5) (x : Fin 5 → ℤ) :
    eNorm (dropICoord i₀ x) ≤ eNorm x := by
  rw [Work.HP.eNorm, Work.HP.eNorm]
  apply Real.sqrt_le_sqrt
  show (∑ j : {j : Fin 5 // j ≠ i₀}, ((x j.1 : ℤ) : ℝ) ^ 2) ≤ ∑ i, ((x i : ℤ) : ℝ) ^ 2
  have h1 : (∑ j : {j : Fin 5 // j ≠ i₀}, ((x j.1 : ℤ) : ℝ) ^ 2)
      = ∑ i ∈ (Finset.univ.image (Subtype.val : {j : Fin 5 // j ≠ i₀} → Fin 5)),
          ((x i : ℤ) : ℝ) ^ 2 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)

/-- The rank of the coordinate projection of a lattice contained in `latOrth a` is unchanged. -/
lemma rk_map_dropICoord (a : Fin 5 → ℤ) (i₀ : Fin 5) (hai : a i₀ ≠ 0)
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ≤ latOrth a) :
    rk (L.map (dropICoord i₀)) = rk L := by
  have hinj : Function.Injective ((dropICoord i₀).comp L.subtype) := by
    intro x y hxy
    apply Subtype.ext
    exact dropICoord_injective_on_latOrth a i₀ hai (hL x.2) (hL y.2) hxy
  have hmap : L.map (dropICoord i₀) = LinearMap.range ((dropICoord i₀).comp L.subtype) := by
    ext x; simp [Submodule.mem_map, LinearMap.mem_range]
  rw [hmap, rk, LinearMap.finrank_range_of_inj hinj]
  rfl

/-- The successive minima do not increase under the coordinate projection. -/
lemma lam_map_dropICoord_le (a : Fin 5 → ℤ) (i₀ : Fin 5) (hai : a i₀ ≠ 0)
    {L : Submodule ℤ (Fin 5 → ℤ)} (hL : L ≤ latOrth a) (i : ℕ) (hi : i ≤ rk L) :
    lam (L.map (dropICoord i₀)) i ≤ lam L i := by
  rw [Work.HP.lam_eq_sInf, Work.HP.lam_eq_sInf]
  refine csInf_le_csInf (Work.HP.bddBelow_lamSet _ i) (Work.HP.lamSet_nonempty L hi) ?_
  intro r hr
  obtain ⟨hr0, f, hfL, hfI, hfr⟩ := hr
  refine ⟨hr0, fun k => dropICoord i₀ (f k), ?_, ?_, ?_⟩
  · intro k; exact Submodule.mem_map.mpr ⟨f k, hfL k, rfl⟩
  · have hdisj : Disjoint (Submodule.span ℤ (Set.range f))
        (LinearMap.ker (dropICoord i₀)) := by
      rw [Submodule.disjoint_def]
      intro x hx hxker
      have hxL : x ∈ L :=
        (Submodule.span_le.mpr (by rintro y ⟨k, rfl⟩; exact hfL k)) hx
      have hxorth : x ∈ latOrth a := hL hxL
      have hx0 : dropICoord i₀ x = 0 := hxker
      exact dropICoord_injective_on_latOrth a i₀ hai hxorth (Submodule.zero_mem _)
        (by rw [hx0]; rfl)
    have := hfI.map hdisj
    simpa [Function.comp_def] using this
  · intro k; exact le_trans (eNorm_dropICoord_le i₀ (f k)) (hfr k)

/-- **Injectivity of the reduction.**  If `L, M` are contained in the hyperplane `a^⊥` and have
the same saturation of the projected lattice, then `M` is primitive only if `L ≤ M`. -/
lemma le_of_satLat_map_eq (a : Fin 5 → ℤ) (i₀ : Fin 5) (hai : a i₀ ≠ 0)
    {L M : Submodule ℤ (Fin 5 → ℤ)} (hMp : IsPrimLat M)
    (hL : L ≤ latOrth a) (hM : M ≤ latOrth a)
    (heq : satLat (L.map (dropICoord i₀)) = satLat (M.map (dropICoord i₀))) : L ≤ M := by
  intro x hx
  have hx' : dropICoord i₀ x ∈ satLat (M.map (dropICoord i₀)) := by
    rw [← heq]
    exact le_satLat _ (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [Work.HP.mem_satLat] at hx'
  obtain ⟨m, hm, hmx⟩ := hx'
  rw [Submodule.mem_map] at hmx
  obtain ⟨y, hyM, hyeq⟩ := hmx
  have hzero : dropICoord i₀ (m • x - y) = 0 := by
    rw [map_sub, map_smul, hyeq]; exact sub_self _
  have hmem : m • x - y ∈ latOrth a :=
    Submodule.sub_mem _ (hL (Submodule.smul_mem _ m hx)) (hM hyM)
  have h00 : m • x - y = 0 :=
    dropICoord_injective_on_latOrth a i₀ hai hmem (Submodule.zero_mem _) hzero
  rw [sub_eq_zero] at h00
  rw [← h00] at hyM
  exact hMp x m hm hyM

/-- **The reduction step.**  The number of primitive rank-3 sublattices of `ℤ^5` inside `a^⊥`
with successive minima bounded by `s` is at most the number of primitive rank-3 sublattices of
`ℤ^{{j // j ≠ i₀}}` with the same successive-minima bounds, for any `i₀` with `a i₀ ≠ 0`. -/
lemma hyper_count_le_of (a : Fin 5 → ℤ) (i₀ : Fin 5) (hai : a i₀ ≠ 0) (s : Fin 3 → ℝ) :
    (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → dotZ x a = 0)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
    ≤ (({L' : Submodule ℤ ({j : Fin 5 // j ≠ i₀} → ℤ) | IsPrimLat L' ∧ rk L' = 3 ∧
        (∀ j : Fin 3, lam L' (j.val + 1) ≤ s j)} :
          Set (Submodule ℤ ({j : Fin 5 // j ≠ i₀} → ℤ))).ncard : ℝ) := by
  classical
  have hnat : (({L : Submodule ℤ (Fin 5 → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
        (∀ j : Fin 3, lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → dotZ x a = 0)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard)
      ≤ (({L' : Submodule ℤ ({j : Fin 5 // j ≠ i₀} → ℤ) | IsPrimLat L' ∧ rk L' = 3 ∧
        (∀ j : Fin 3, lam L' (j.val + 1) ≤ s j)} :
          Set (Submodule ℤ ({j : Fin 5 // j ≠ i₀} → ℤ))).ncard) := by
    refine Set.ncard_le_ncard_of_injOn
      (fun L : Submodule ℤ (Fin 5 → ℤ) => satLat (L.map (dropICoord i₀))) ?_ ?_
      (Sig2.Tset_finite (ι := {j : Fin 5 // j ≠ i₀}) 3 s)
    · intro L hL
      obtain ⟨hLp, hLrk, hLlam, hLorth⟩ := hL
      have hLle : L ≤ latOrth a := le_latOrth_of_dotZ a hLorth
      have hrkm : rk (L.map (dropICoord i₀)) = 3 := by
        rw [rk_map_dropICoord a i₀ hai hLle, hLrk]
      refine ⟨Work.HP.isPrimLat_satLat _, ?_, ?_⟩
      · rw [numaux.rk_satLat, hrkm]
      · intro j
        have hj3 : j.val + 1 ≤ 3 := by have := j.isLt; omega
        have h1 : lam (satLat (L.map (dropICoord i₀))) (j.val + 1)
            ≤ lam (L.map (dropICoord i₀)) (j.val + 1) :=
          lam_antitone_of_le (le_satLat _) (by rw [hrkm]; exact hj3)
        have h2 : lam (L.map (dropICoord i₀)) (j.val + 1) ≤ lam L (j.val + 1) :=
          lam_map_dropICoord_le a i₀ hai hLle (j.val + 1) (by rw [hLrk]; exact hj3)
        exact le_trans h1 (le_trans h2 (hLlam j))
    · intro L hL M hM heq
      obtain ⟨hLp, -, -, hLorth⟩ := hL
      obtain ⟨hMp, -, -, hMorth⟩ := hM
      have hLle : L ≤ latOrth a := le_latOrth_of_dotZ a hLorth
      have hMle : M ≤ latOrth a := le_latOrth_of_dotZ a hMorth
      exact le_antisymm
        (le_of_satLat_map_eq a i₀ hai hMp hLle hMle heq)
        (le_of_satLat_map_eq a i₀ hai hLp hMle hLle heq.symm)
  exact_mod_cast hnat

/-- The paper's lattice count in dimension `4`: number of primitive rank-3 sublattices of `ℤ^4`
with `λ_{j+1} ≤ s j` is `O(s 0^6 · s 1^4 · s 2^2)`. -/
lemma numLattices_card4 (ι : Type*) [Fintype ι] [DecidableEq ι] (hcard : Fintype.card ι = 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Fin 3 → ℝ), (∀ j : Fin 3, 1 ≤ s j) →
      (({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = 3 ∧
          (∀ j : Fin 3, lam L (j.val + 1) ≤ s j)} : Set (Submodule ℤ (ι → ℤ))).ncard : ℝ)
        ≤ K * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) := by
  obtain ⟨Kmk, hKmkpos, hmink⟩ := Sig2.minkowski_prod (ι := ι)
  obtain ⟨K, hKpos, hK⟩ := Sig2.num_lattices_of (ι := ι) Kmk (le_of_lt hKmkpos) hmink
  refine ⟨K, hKpos, fun s hs => ?_⟩
  have h := hK 3 s hs
  rw [hcard] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Fin.prod_univ_three]; norm_num

/-- Number of primitive rank-3 sublattices of `ℤ^5` inside a fixed hyperplane `a^⊥` (a ≠ 0) with
successive minima bounded by `s`, uniformly in `a`.

Suggested route (a uniform reduction to `Work.HP.Sig2.num_lattices_of` at `ι = {j // j ≠ i₀}`):
pick `i₀` with `a i₀ ≠ 0` and let `π : ℤ^5 → ({j // j ≠ i₀} → ℤ)` drop the `i₀`-coordinate; `π` is
injective on the hyperplane `a^⊥ ⊗ ℚ`. Map `L ↦ V' := π_ℚ(span_ℚ L)`; this is injective, and
`λ_i(V' ∩ ℤ^4) ≤ λ_i(π L) ≤ λ_i(L) ≤ s i` (images of λ-realizers have no larger norm, and `π`
preserves linear independence on the hyperplane). Hence the count is at most the number of
primitive rank-3 sublattices of `ℤ^4` with `λ_i ≤ s i`, which is
`K * s0^6 * s1^4 * s2^2` by `num_lattices_of` (`ι = {j // j ≠ i₀}`, `Fintype.card = 4`). -/
theorem hypLatCount : ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin 5 → ℤ), a ≠ 0 →
    ∀ (s : Fin 3 → ℝ), 1 ≤ s 0 → s 0 ≤ s 1 → s 1 ≤ s 2 →
    (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
        (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
        (∀ x : Fin 5 → ℤ, x ∈ L → Work.HP.dotZ x a = 0)} : Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
      ≤ C * ((s 0) ^ 6 * (s 1) ^ 4 * (s 2) ^ 2) := by
  classical
  have hcardJ : ∀ i : Fin 5, Fintype.card {j : Fin 5 // j ≠ i} = 4 := by
    intro i
    rw [Fintype.card_subtype_compl (fun j : Fin 5 => j = i)]
    simp [Fintype.card_fin]
  have hK : ∀ i : Fin 5, ∃ K : ℝ, 0 < K ∧ ∀ (s : Fin 3 → ℝ), (∀ j : Fin 3, 1 ≤ s j) →
      ((({L' : Submodule ℤ ({j : Fin 5 // j ≠ i} → ℤ) | IsPrimLat L' ∧ rk L' = 3 ∧
          (∀ j : Fin 3, lam L' (j.val + 1) ≤ s j)} :
            Set (Submodule ℤ ({j : Fin 5 // j ≠ i} → ℤ))).ncard : ℝ)
        ≤ K * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2)) :=
    fun i => numLattices_card4 {j : Fin 5 // j ≠ i} (hcardJ i)
  choose Kc hKc using hK
  set C : ℝ := (Finset.univ : Finset (Fin 5)).sup' Finset.univ_nonempty Kc with hCdef
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]
    exact lt_of_lt_of_le (hKc 0).1 (Finset.le_sup' Kc (Finset.mem_univ 0))
  · intro a ha s hs0 hs01 hs12
    obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      exact ⟨i, by simpa using hi⟩
    have hred := hyper_count_le_of a i₀ hi₀ s
    have hs1 : ∀ j : Fin 3, 1 ≤ s j := by
      intro j
      fin_cases j
      · exact hs0
      · exact le_trans hs0 hs01
      · exact le_trans (le_trans hs0 hs01) hs12
    have hb := (hKc i₀).2 s hs1
    have hCle : Kc i₀ ≤ C := by rw [hCdef]; exact Finset.le_sup' Kc (Finset.mem_univ i₀)
    have hnonneg : 0 ≤ s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2 := by
      have h0 : 0 ≤ s 0 := le_trans zero_le_one hs0
      have h1 : 0 ≤ s 1 := le_trans h0 hs01
      have h2 : 0 ≤ s 2 := le_trans h1 hs12
      positivity
    calc (({L : Submodule ℤ (Fin 5 → ℤ) | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
          (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
          (∀ x : Fin 5 → ℤ, x ∈ L → Work.HP.dotZ x a = 0)} :
            Set (Submodule ℤ (Fin 5 → ℤ))).ncard : ℝ)
        ≤ (({L' : Submodule ℤ ({j : Fin 5 // j ≠ i₀} → ℤ) | IsPrimLat L' ∧ rk L' = 3 ∧
            (∀ j : Fin 3, lam L' (j.val + 1) ≤ s j)} :
              Set (Submodule ℤ ({j : Fin 5 // j ≠ i₀} → ℤ))).ncard : ℝ) := hred
      _ ≤ Kc i₀ * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) := hb
      _ ≤ C * (s 0 ^ 6 * s 1 ^ 4 * s 2 ^ 2) := mul_le_mul_of_nonneg_right hCle hnonneg

end Work.HP.MDEstimates
