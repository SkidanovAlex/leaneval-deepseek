import Mathlib
import Submission.Commons.LinearAlgebra.Net.compress_slice_net

set_option autoImplicit false
open scoped BigOperators

namespace Commons.LinearAlgebra.Net

open Finset

/-!
# Net for the compressible set

The `(δ,ν)`-compressible set (unit vectors within distance `ν` of a vector of
support at most `⌊δ·n⌋`) is a union, over supports `S` of cardinality
`⌊δ·n⌋`, of the `ν`-neighbourhoods of the unit spheres of the coordinate
subspaces `V_S`.  Each such piece admits an `R`-net of cardinality at most
`(8C/R)^|S|` (a net on the unit sphere of `V_S` with mesh `R/8`), so the
whole compressible set admits a net of cardinality at most
`(n.choose ⌊δn⌋) · (C₀/R)^⌊δn⌋` with `C₀ := 8C`.
-/

/-- When `⌊δn⌋₊ = 0` the `(δ,ν)`-compressible set is empty (for `ν < 1`). -/
lemma no_compressible_of_floor_zero {n : ℕ} {δ ν : ℝ} {x : Fin n → ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hδn : δ * (n : ℝ) < 1) : ¬ compressible δ ν x := by
  intro hx
  rcases hx with ⟨hx1, hz⟩
  rcases hz with ⟨z, hzsq, hzsupp⟩
  have hcard0 : (Finset.univ.filter (fun i => z i ≠ 0)).card = 0 := by
    have hlt : ((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) < 1 :=
      lt_of_le_of_lt hzsupp hδn
    by_contra hne
    have hpos : 0 < (Finset.univ.filter (fun i => z i ≠ 0)).card := Nat.pos_of_ne_zero hne
    have h1r : (1 : ℝ) ≤ ((Finset.univ.filter (fun i => z i ≠ 0)).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hpos)
    linarith
  have hz0 : z = 0 := by
    ext i
    have hc0 : supp z = ∅ := by
      exact Finset.card_eq_zero.mp (by simpa [supp] using hcard0)
    have hi : i ∉ supp z := by rw [hc0]; simp
    exact (not_mem_supp z).mp hi
  have hxle : sqNorm x ≤ ν^2 := by simpa [hz0] using hzsq
  have hxeq : sqNorm x = 1 := hx1
  nlinarith [sqNorm_nonneg x]

/-- A unit vector supported on a set `S` with `(S.card : ℝ) ≤ δ·n` is
`(δ,ν)`-compressible (take it as its own sparse approximation). -/
lemma compressible_of_unit_supported {n : ℕ} {δ ν : ℝ} {S : Finset (Fin n)}
    {y : Fin n → ℝ} (hy1 : sqNorm y = 1) (hys : ∀ i : Fin n, i ∉ S → y i = 0)
    (hSδ : (S.card : ℝ) ≤ δ * (n : ℝ)) : compressible δ ν y := by
  refine ⟨hy1, ⟨y, ?_, ?_⟩⟩
  · have hz : sqNorm (y - y) = 0 := by simp [sqNorm]
    rw [hz]
    exact sq_nonneg ν
  · change ((supp y).card : ℝ) ≤ δ * (n : ℝ)
    have hsuppS : supp y ⊆ S := by
      intro i hi
      by_contra hnot
      exact (mem_supp y).mp hi (hys i hnot)
    have hcardle : (supp y).card ≤ S.card := Finset.card_le_card hsuppS
    have hcast : ((supp y).card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcardle
    exact le_trans hcast hSδ

/-- For a fixed support `S`, the `ν`-neighbourhood of the unit sphere of `V_S`
admits an `R`-net (inside the sphere of `V_S`, hence inside the compressible
set when `S.card ≤ δ·n`): the net points are the elements of an `η`-net `G`
of the unit sphere of `V_S` with `2η + 2ν + ν² ≤ R`. -/
lemma perS_compressible_cover {n : ℕ} {δ ν : ℝ} {S : Finset (Fin n)} {η R : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hR0 : 0 ≤ R) (hη0 : 0 ≤ η)
    (hSδ : (S.card : ℝ) ≤ δ * (n : ℝ))
    (hη_ν : 2 * η + 2 * ν + ν^2 ≤ R)
    (G : Finset (Fin n → ℝ))
    (hG1 : ∀ g ∈ G, sqNorm g = 1)
    (hG2 : ∀ g ∈ G, ∀ i : Fin n, i ∉ S → g i = 0)
    (hG3 : ∀ u : Fin n → ℝ, sqNorm u = 1 → (∀ i : Fin n, i ∉ S → u i = 0) →
           ∃ g ∈ G, nrm (u - g) ≤ η) :
    (∀ g ∈ G, compressible δ ν g) ∧
    (∀ x : Fin n → ℝ, compressible δ ν x →
       (∃ z : Fin n → ℝ, sqNorm (x - z) ≤ ν^2 ∧ (∀ i : Fin n, i ∉ S → z i = 0)) →
       ∃ g ∈ G, sqNorm (g - x) ≤ R^2) := by
  classical
  constructor
  · intro g hgG
    exact compressible_of_unit_supported (hG1 g hgG) (hG2 g hgG) hSδ
  · intro x hx hxz
    rcases hx with ⟨hx1, hz⟩
    rcases hxz with ⟨z, hzsq, hzS⟩
    have hvx : nrm (x - res S x) ≤ ν := nrm_sub_res_le_of_sqNorm_sub S x z ν hν0 hzS hzsq
    have hab := alpha_bounds S (x := x) (ν := ν) hx1 hvx hν0 hν1
    have hresne : res S x ≠ 0 := by
      intro h
      exact hab.2.2 ((nrm_eq_zero_iff (res S x)).mpr h)
    let u : Fin n → ℝ := dir S x
    have hu1 : sqNorm u = 1 := by
      dsimp [u]
      exact sqNorm_dir_eq_one S hresne
    have hsup : ∀ i : Fin n, i ∉ S → u i = 0 := by
      intro i hi
      dsimp [u]
      exact dir_supported S x hi
    rcases hG3 u hu1 hsup with ⟨g, hgG, hdu⟩
    refine ⟨g, hgG, ?_⟩
    have hresg : res S g = g := res_self_of_supp S (hG2 g hgG)
    have hv2 : nrm (g - res S g) ≤ ν := by
      rw [hresg]
      simp [nrm, sqNorm]
      exact hν0
    have hng1 : nrm g = 1 := (sqNorm_eq_one_of_nrm g).mp (hG1 g hgG)
    have hdirg : dir S g = g := by
      unfold dir
      rw [hresg, hng1]
      simp
    have hd2 : nrm (dir S g - g) ≤ η := by
      rw [hdirg]
      simp [nrm, sqNorm]
      exact hη0
    have hdiam := bucket_diam S (x₁ := x) (x₂ := g) (p := g) η ν hν0 hν1 hx1
      (hG1 g hgG) hvx hv2 hdu hd2
    have hngx : nrm (x - g) ≤ R := le_trans hdiam hη_ν
    have hgxn : nrm (g - x) = nrm (x - g) := by
      rw [← nrm_neg (g - x)]
      congr 1
      ext i
      simp
    have hnn : nrm (g - x) ≤ R := by rwa [hgxn]
    exact sqNorm_le_sq_of_nrm_le hR0 hnn

/-- A net of the whole `(δ,ν)`-compressible set: every compressible vector is
within distance `R` of a compressible net point, and the net has cardinality at
most `(n.choose ⌊δn⌋) · (C₀/R)^⌊δn⌋`. -/
theorem compressible_net :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ {δ ν R : ℝ}, 0 < δ → δ ≤ 1 → 0 < ν → ν ≤ R / 4 → 0 < R → R ≤ 1 →
        ∃ Net : Finset (Fin n → ℝ),
          (∀ x : Fin n → ℝ, Commons.LinearAlgebra.Net.compressible δ ν x →
              ∃ y ∈ Net, Commons.LinearAlgebra.Net.compressible δ ν y ∧
                Commons.LinearAlgebra.Net.sqNorm (y - x) ≤ R^2) ∧
          (Net.card : ℝ) ≤ (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) *
            (C₀ / R) ^ ⌊δ * (n : ℝ)⌋₊ := by
  classical
  rcases exists_support_unit_net with ⟨C, hC1, hnets⟩
  let C₀ : ℝ := max 1 (8 * C)
  have hC₀ge1 : 1 ≤ C₀ := by dsimp [C₀]; simp
  have h8C : 8 * C ≤ C₀ := by
    dsimp [C₀]
    exact le_max_right _ _
  refine ⟨C₀, hC₀ge1, ?_⟩
  intro n hn δ ν R hδ0 hδ1 hν0 hνR hR0 hR1
  let k : ℕ := ⌊δ * (n : ℝ)⌋₊
  let η : ℝ := R / 8
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hη1 : η ≤ 1 := by dsimp [η]; nlinarith
  have hδn0 : 0 ≤ δ * (n : ℝ) := by positivity
  have hkδ : (k : ℝ) ≤ δ * (n : ℝ) := by
    dsimp [k]
    exact Nat.floor_le hδn0
  have hδn_le : δ * (n : ℝ) ≤ (n : ℝ) := by nlinarith
  have hkn : k ≤ n := by
    have hkr : (k : ℝ) ≤ (n : ℝ) := le_trans hkδ hδn_le
    exact_mod_cast hkr
  have hνlt1 : ν < 1 := by nlinarith
  by_cases hk0 : k = 0
  · -- empty compressible set
    have hδn1 : δ * (n : ℝ) < 1 := by
      have h1 : δ * (n : ℝ) < (⌊δ * (n : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (δ * (n : ℝ))
      have hk0r : (⌊δ * (n : ℝ)⌋₊ : ℝ) = 0 := by
        dsimp [k] at hk0
        exact_mod_cast hk0
      nlinarith
    refine ⟨∅, ?_, ?_⟩
    · intro x hx
      exfalso
      exact no_compressible_of_floor_zero (le_of_lt hν0) hνlt1 hδn1 hx
    · -- cardinality of the empty net
      have hfloor : ⌊δ * (n : ℝ)⌋₊ = 0 := by
        dsimp [k] at hk0
        exact hk0
      rw [hfloor]
      simp
  · -- k ≥ 1 : build the union of per-support nets
    have hkpos : 0 < k := by
      by_contra h
      exact hk0 (Nat.eq_zero_of_not_pos h)
    let All : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
    have hAllcard : All.card = n.choose k := by
      dsimp [All]
      simp
    have hη_ν : 2 * η + 2 * ν + ν^2 ≤ R := by
      dsimp [η]
      nlinarith
    have hcoverS : ∀ S : Finset (Fin n), S.card = k →
        ∃ NetS : Finset (Fin n → ℝ),
          (∀ y ∈ NetS, compressible δ ν y) ∧
          (∀ x : Fin n → ℝ, compressible δ ν x →
             (∃ z : Fin n → ℝ, sqNorm (x - z) ≤ ν^2 ∧ (∀ i : Fin n, i ∉ S → z i = 0)) →
             ∃ y ∈ NetS, sqNorm (y - x) ≤ R^2) ∧
          ((NetS.card : ℝ) ≤ (8 * C / R)^k) := by
        intro S hSk
        rcases hnets n S η hη0 hη1 with ⟨G, hG1hG2, hG3, hGcard0⟩
        have hSδ : (S.card : ℝ) ≤ δ * (n : ℝ) := by
          calc
            (S.card : ℝ) = (k : ℝ) := by rw [hSk]
            _ ≤ δ * (n : ℝ) := hkδ
        have hG1 : ∀ g ∈ G, sqNorm g = 1 := fun g hg => (hG1hG2 g hg).1
        have hG2 : ∀ g ∈ G, ∀ i : Fin n, i ∉ S → g i = 0 := fun g hg i hi => (hG1hG2 g hg).2 i hi
        have hGcardk : (G.card : ℝ) ≤ (C / η)^k := by
          simpa [hSk, η] using hGcard0
        have hbase : C / η = 8 * C / R := by
          dsimp [η]
          field_simp [show R ≠ 0 by linarith]
        have hGcard8 : (G.card : ℝ) ≤ (8 * C / R)^k := by
          simpa [hbase] using hGcardk
        rcases perS_compressible_cover (le_of_lt hν0) hνlt1 (le_of_lt hR0) (le_of_lt hη0) hSδ hη_ν
          G hG1 hG2 hG3 with ⟨hGcomp, hGcov⟩
        exact ⟨G, hGcomp, hGcov, hGcard8⟩
    let NS : (Finset (Fin n)) → Finset (Fin n → ℝ) := fun S =>
      if hS : S.card = k then Classical.choose (hcoverS S hS) else ∅
    let Net : Finset (Fin n → ℝ) := All.biUnion NS
    refine ⟨Net, ?_, ?_⟩
    · -- covering
      intro x hx
      have hx1 : sqNorm x = 1 := hx.1
      rcases hx.2 with ⟨z, hzsq, hzsupp⟩
      have hsuppk : (supp z).card ≤ k := by
        apply Nat.le_floor
        simpa [supp] using hzsupp
      have hkn' : k ≤ Fintype.card (Fin n) := by simpa using hkn
      rcases exists_superset_card_eq (T := supp z) (k := k) hsuppk hkn' with ⟨S, hTS, hSk⟩
      have hS_mem : S ∈ All := by
        dsimp [All]
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hSk⟩
      have hzS : ∀ i : Fin n, i ∉ S → z i = 0 := by
        intro i hi
        have : i ∉ supp z := fun hiT => hi (hTS hiT)
        exact (not_mem_supp z).mp this
      have hpropS := Classical.choose_spec (hcoverS S hSk)
      rcases hpropS with ⟨hScomp, hScover, hScard⟩
      rcases hScover x hx ⟨z, hzsq, hzS⟩ with ⟨y, hyNS, hybound⟩
      refine ⟨y, ?_, ?_⟩
      · dsimp [Net]
        have hNS : NS S = Classical.choose (hcoverS S hSk) := by
          dsimp [NS]
          rw [dif_pos hSk]
        exact Finset.mem_biUnion.mpr ⟨S, hS_mem, by simpa [hNS] using hyNS⟩
      · have hNS : NS S = Classical.choose (hcoverS S hSk) := by
          dsimp [NS]
          rw [dif_pos hSk]
        exact ⟨hScomp y (by simpa [hNS] using hyNS), hybound⟩
    · -- cardinality
      dsimp [Net]
      calc
        ((All.biUnion NS).card : ℝ)
            ≤ ∑ S ∈ All, ((NS S).card : ℝ) := by
              have h0 := Finset.card_biUnion_le (s := All) (t := NS)
              have h1 : ((All.biUnion NS).card : ℝ) ≤ ((∑ S ∈ All, (NS S).card) : ℝ) := by exact_mod_cast h0
              simpa [Finset.sum_apply, Finset.sum_attach] using h1
        _ ≤ ∑ S ∈ All, (8 * C / R)^k := by
              apply Finset.sum_le_sum
              intro S hS
              have hSk : S.card = k := (Finset.mem_powersetCard.mp hS).2
              have hNS : NS S = Classical.choose (hcoverS S hSk) := by
                dsimp [NS]
                rw [dif_pos hSk]
              have hc : (NS S).card ≤ (8 * C / R)^k := by
                rw [hNS]
                exact (Classical.choose_spec (hcoverS S hSk)).2.2
              exact_mod_cast hc
        _ = (All.card : ℝ) * (8 * C / R)^k := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((n.choose k : ℝ)) * (8 * C / R)^k := by
              rw [hAllcard]
        _ ≤ (n.choose k : ℝ) * (C₀ / R)^k := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply pow_le_pow_left₀
              · positivity
              · exact div_le_div_of_nonneg_right h8C (le_of_lt hR0)
        _ = (n.choose ⌊δ * (n : ℝ)⌋₊ : ℝ) * (C₀ / R) ^ ⌊δ * (n : ℝ)⌋₊ := by
              dsimp [k]

end Commons.LinearAlgebra.Net
