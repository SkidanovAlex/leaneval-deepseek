import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.MDEstimates.mu_sum_aux
import Submission.Work.HP.MDEstimates.muXY_le
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Lat.span_pair_lattice

/-!
# Bound for `μ(x,y) / det Γ_{x,y}`

Browning--Le Boudec--Sawin, *The Hasse principle for random Fano hypersurfaces* (Annals 2023), §4:
given the lower bound `det Γ_{x,y} ≥ 𝔡₂ ‖x‖^{d-1} ‖y‖^{d-1} / C` (the hypothesis `hdet`, coming
from the archimedean `detGam_lower`), the threshold

`μ(x,y) = 3n² max(𝔡₂/𝔡₃, ‖x‖‖y‖/𝔡₂²)`,  `𝔡_r = dmin r {x,y}`,

satisfies, with `𝔡₂ ≤ ‖x‖‖y‖` and `𝔡_r ≥ 1`,

`μ(x,y)/det Γ_{x,y} ≤ 3n² C (1/(𝔡₂𝔡₃‖x‖^{d-2}‖y‖^{d-2}) + 1/(𝔡₂²‖x‖^{d-2}‖y‖^{d-2}))`.

The proof splits `μ` through its maximum via `muXY_le_split` and treats the two terms with the
elementary real inequality `mu_div_det_core`.
-/

set_option autoImplicit false
noncomputable section

open Work.HP

namespace Work.HP.MDEstimates

/-- `dmin` is nonnegative: `sInf` of a set of nonnegative real numbers (or `sInf ∅ = 0`). -/
private lemma dmin_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  rw [Work.HP.dmin]
  by_cases hne : ({D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D} : Set ℝ).Nonempty
  · exact le_csInf hne (fun D hD => by obtain ⟨L, _, _, rfl⟩ := hD; exact detL_nonneg L)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

/-- If `S` is contained in *some* rank-`r` sublattice, then `dmin r S ≥ 1` (all covolumes of
integral lattices are at least one). -/
private lemma one_le_dmin_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ)
    (S : Set (ι → ℤ)) (L : Submodule ℤ (ι → ℤ)) (hr : rk L = r) (hS : S ⊆ L) :
    1 ≤ dmin r S := by
  rw [Work.HP.dmin]
  refine le_csInf ⟨detL L, L, hr, hS, rfl⟩ ?_
  rintro D ⟨L', _, _, rfl⟩
  exact Lat.detL_ge_one L'

/-- **Real-arithmetic core.**  With `d₂ ≥ 1`, `d₂ ≤ Nx·Ny`, `0 ≤ d₃`, all of `C, G, Nx, Ny` positive,
and `d₂ · Nx^{k+1} · Ny^{k+1} ≤ C·G`, the two summands of `μ/G` are dominated by the two terms of
the target bound. -/
private lemma mu_div_det_core_aux (C d2 d3 Nx Ny G : ℝ) (k : ℕ)
    (hC : 0 < C) (hG : 0 < G) (hNx : 0 < Nx) (hNy : 0 < Ny)
    (hd2 : 1 ≤ d2) (hd3 : 0 ≤ d3) (hd2ub : d2 ≤ Nx * Ny)
    (hdet : d2 * Nx ^ (k + 1) * Ny ^ (k + 1) ≤ C * G) :
    (d2 / d3 + Nx * Ny / d2 ^ 2) / G ≤
      C * (1 / (d2 * d3 * Nx ^ k * Ny ^ k) + 1 / (d2 ^ 2 * Nx ^ k * Ny ^ k)) := by
  have hNxk : 0 < Nx ^ k := pow_pos hNx k
  have hNyk : 0 < Ny ^ k := pow_pos hNy k
  -- `hdet` rewritten as `d2 · P · Q ≤ C · G` with `P = Nx^k·Ny^k`, `Q = Nx·Ny`
  have hdet' : d2 * (Nx ^ k * Ny ^ k) * (Nx * Ny) ≤ C * G := by
    rw [pow_succ, pow_succ] at hdet
    linarith [hdet]
  -- `Q·P ≤ C·G`
  have hQP : (Nx * Ny) * (Nx ^ k * Ny ^ k) ≤ C * G := by
    have h1 : 1 * ((Nx ^ k * Ny ^ k) * (Nx * Ny)) ≤ d2 * ((Nx ^ k * Ny ^ k) * (Nx * Ny)) :=
      mul_le_mul_of_nonneg_right hd2 (by positivity)
    linarith [h1, hdet']
  -- `d2²·P ≤ C·G`
  have hd2sqP : d2 ^ 2 * (Nx ^ k * Ny ^ k) ≤ C * G := by
    have h1 : d2 * (d2 * (Nx ^ k * Ny ^ k)) ≤ (Nx * Ny) * (d2 * (Nx ^ k * Ny ^ k)) :=
      mul_le_mul_of_nonneg_right hd2ub (by positivity)
    linarith [h1, hdet']
  -- first summand: `d2/(d3·G) ≤ C/(d2·d3·P)`
  have hA : d2 / (d3 * G) ≤ C / (d2 * d3 * Nx ^ k * Ny ^ k) := by
    rcases lt_or_eq_of_le hd3 with h3 | h3
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hd2sqP, h3]
    · rw [← h3]; simp
  -- second summand: `Q/(d2²·G) ≤ C/(d2²·P)`
  have hB : Nx * Ny / (d2 ^ 2 * G) ≤ C / (d2 ^ 2 * Nx ^ k * Ny ^ k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : d2 ^ 2 * ((Nx * Ny) * (Nx ^ k * Ny ^ k)) ≤ d2 ^ 2 * (C * G) :=
      mul_le_mul_of_nonneg_left hQP (sq_nonneg d2)
    nlinarith [h1]
  calc (d2 / d3 + Nx * Ny / d2 ^ 2) / G
      = d2 / (d3 * G) + (Nx * Ny) / (d2 ^ 2 * G) := by rw [add_div, div_div, div_div]
    _ ≤ C / (d2 * d3 * Nx ^ k * Ny ^ k) + C / (d2 ^ 2 * Nx ^ k * Ny ^ k) := add_le_add hA hB
    _ = C * (1 / (d2 * d3 * Nx ^ k * Ny ^ k) + 1 / (d2 ^ 2 * Nx ^ k * Ny ^ k)) := by
        simp only [div_eq_mul_inv, one_mul]; ring

theorem mu_div_det_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (C : ℝ) (hC : 0 < C)
    (x y : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y)
    (hind : LinearIndependent ℤ ![x, y])
    (hdet : Work.HP.dmin 2 {x, y} * Work.HP.eNorm x ^ (d - 1) * Work.HP.eNorm y ^ (d - 1)
      ≤ C * Work.HP.detL (Work.HP.Gam d n x y)) :
    Work.HP.muXY n x y / Work.HP.detL (Work.HP.Gam d n x y)
      ≤ 3 * (n : ℝ) ^ 2 * C *
          (1 / (Work.HP.dmin 2 {x, y} * Work.HP.dmin 3 {x, y} *
                Work.HP.eNorm x ^ (d - 2) * Work.HP.eNorm y ^ (d - 2))
           + 1 / (Work.HP.dmin 2 {x, y} ^ 2 *
                Work.HP.eNorm x ^ (d - 2) * Work.HP.eNorm y ^ (d - 2))) := by
  obtain ⟨L, hLrk, hxL, hyL, hLdet⟩ := Lat.span_pair_lattice x y hind
  have hsub : ({x, y} : Set (Fin (n + 1) → ℤ)) ⊆ L := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hxL
    · exact hyL
  have hd2one : 1 ≤ dmin 2 {x, y} := one_le_dmin_of_le 2 {x, y} L hLrk hsub
  have hd2le : dmin 2 {x, y} ≤ eNorm x * eNorm y :=
    (dmin_le_detL 2 {x, y} L hLrk hsub).trans hLdet
  have hd3nn : 0 ≤ dmin 3 {x, y} := dmin_nonneg 3 {x, y}
  have hNx : 0 < eNorm x := eNorm_pos_of_ne_zero (isPrim_ne_zero hx)
  have hNy : 0 < eNorm y := eNorm_pos_of_ne_zero (isPrim_ne_zero hy)
  -- positivity of `det Γ`
  have hG : 0 < detL (Gam d n x y) := by
    have hpos : 0 < dmin 2 {x, y} * eNorm x ^ (d - 1) * eNorm y ^ (d - 1) :=
      mul_pos (mul_pos (lt_of_lt_of_le one_pos hd2one) (pow_pos hNx _)) (pow_pos hNy _)
    have h3 : 0 < C * detL (Gam d n x y) := lt_of_lt_of_le hpos hdet
    exact pos_of_mul_pos_right h3 (le_of_lt hC)
  -- `hdet` in the form required by the core lemma
  have hdet' : dmin 2 {x, y} * eNorm x ^ (d - 2 + 1) * eNorm y ^ (d - 2 + 1)
      ≤ C * detL (Gam d n x y) := by
    have h1 : d - 2 + 1 = d - 1 := by omega
    rw [h1]
    exact hdet
  have hcore := mu_div_det_core_aux C (dmin 2 {x, y}) (dmin 3 {x, y}) (eNorm x) (eNorm y)
      (detL (Gam d n x y)) (d - 2) hC hG hNx hNy hd2one hd3nn hd2le hdet'
  have hA : 0 ≤ dmin 2 {x, y} / dmin 3 {x, y} := div_nonneg (by linarith [hd2one]) hd3nn
  have hB : 0 ≤ eNorm x * eNorm y / dmin 2 {x, y} ^ 2 :=
    div_nonneg (mul_nonneg (le_of_lt hNx) (le_of_lt hNy)) (sq_nonneg _)
  have hs : muXY n x y / detL (Gam d n x y) ≤
      3 * (n : ℝ) ^ 2 * ((dmin 2 {x, y} / dmin 3 {x, y} +
        eNorm x * eNorm y / dmin 2 {x, y} ^ 2) / detL (Gam d n x y)) := by
    have h1 : muXY n x y / detL (Gam d n x y) ≤
        (3 * (n : ℝ) ^ 2 * (dmin 2 {x, y} / dmin 3 {x, y} +
          eNorm x * eNorm y / dmin 2 {x, y} ^ 2)) / detL (Gam d n x y) :=
      div_le_div_of_nonneg_right (muXY_le_split n hA hB) (le_of_lt hG)
    rwa [mul_div_assoc] at h1
  calc muXY n x y / detL (Gam d n x y)
      ≤ 3 * (n : ℝ) ^ 2 * ((dmin 2 {x, y} / dmin 3 {x, y} +
          eNorm x * eNorm y / dmin 2 {x, y} ^ 2) / detL (Gam d n x y)) := hs
    _ ≤ 3 * (n : ℝ) ^ 2 * (C * (1 / (dmin 2 {x, y} * dmin 3 {x, y} *
            eNorm x ^ (d - 2) * eNorm y ^ (d - 2)) +
          1 / (dmin 2 {x, y} ^ 2 * eNorm x ^ (d - 2) * eNorm y ^ (d - 2)))) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 3 * (n : ℝ) ^ 2 * C * (1 / (dmin 2 {x, y} * dmin 3 {x, y} *
            eNorm x ^ (d - 2) * eNorm y ^ (d - 2)) +
          1 / (dmin 2 {x, y} ^ 2 * eNorm x ^ (d - 2) * eNorm y ^ (d - 2))) := by ring

end Work.HP.MDEstimates
