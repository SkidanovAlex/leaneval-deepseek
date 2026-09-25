import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le_two
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.bmRow

namespace Work.NN.Newton.FTedat

open scoped NNReal ENNReal Topology
open Set Filter
open Work.CR.Flat

noncomputable section

/-! ## Auxiliary facts -/

/-- The derivative of a function vanishes at a point outside its (closed) support. -/
private lemma fderiv_eq_zero_of_notMem_tsupport {n : ℕ} {u : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hz : z ∉ tsupport u) : fderiv ℝ u z = 0 := by
  have hopen : (tsupport u)ᶜ ∈ 𝓝 z := (isClosed_tsupport u).isOpen_compl.mem_nhds hz
  have h0 : u =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have hd : HasFDerivAt u (0 : (Fin n → ℂ) →L[ℝ] ℂ) z :=
    (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq h0
  simpa using hd.fderiv

/-- If the closed support of `u` lies in the polydisc `polydisc 0 r`, then `∂̄_a u` vanishes
off that polydisc. -/
private lemma dbarCoord_eq_zero_of_tsupport_subset {n : ℕ} {u : (Fin n → ℂ) → ℂ}
    {r : Fin n → ℝ} (h : tsupport u ⊆ polydisc 0 r) (a : Fin n) {z : Fin n → ℂ}
    (hz : z ∉ polydisc 0 r) : dbarCoord a u z = 0 := by
  have hz' : z ∉ tsupport u := fun hc => hz (h hc)
  rw [dbarCoord, fderiv_eq_zero_of_notMem_tsupport hz']
  simp

/-- Extract the sup bound on `Ω` from a bound on the `C^{0,α}` norm. -/
private lemma sup_le_of_holderNorm {n : ℕ} {α : ℝ} {u : (Fin n → ℂ) → ℂ}
    {Ω : Set (Fin n → ℂ)} {N : ℝ} (hN0 : 0 ≤ N)
    (h : holderNorm 0 α u Ω ≤ ENNReal.ofReal N) :
    ∀ z ∈ Ω, ‖u z‖ ≤ N := by
  intro z hz
  have h1 := norm_apply_le_holderNorm 0 α u Ω hz
  exact (ENNReal.ofReal_le_ofReal_iff hN0).mp (le_trans h1 h)

/-- Extract the Hölder bound on `Ω` from a bound on the `C^{0,α}` norm. -/
private lemma sub_le_of_holderNorm {n : ℕ} {α : ℝ} {u : (Fin n → ℂ) → ℂ}
    {Ω : Set (Fin n → ℂ)} {N : ℝ} (hN0 : 0 ≤ N)
    (h : holderNorm 0 α u Ω ≤ ENNReal.ofReal N) :
    ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ‖u x - u y‖ ≤ N * ‖x - y‖ ^ α := by
  intro x hx y hy hxy
  have hd : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  have h1 := le_holderSeminorm 0 α u Ω hx hy hxy
  have h2 : holderSeminorm 0 α u Ω ≤ ENNReal.ofReal N :=
    le_trans (holderSeminorm_le_holderNorm 0 α u Ω le_rfl) h
  have h3 : ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 u Ω x - iteratedFDerivWithin ℝ 0 u Ω y‖
      / ‖x - y‖ ^ α) ≤ ENNReal.ofReal N := le_trans h1 h2
  have h4 : ‖iteratedFDerivWithin ℝ 0 u Ω x - iteratedFDerivWithin ℝ 0 u Ω y‖ / ‖x - y‖ ^ α
      ≤ N := (ENNReal.ofReal_le_ofReal_iff hN0).mp h3
  rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub] at h4
  exact (div_le_iff₀ hd).mp h4

/-- **Pointwise bound for a product `u * v`.**  If `u` is bounded by `Nu`, `α`-Hölder with
constant `Nu` on all of `ℂⁿ` and vanishes off the polydisc `polydisc 0 r`, while `v` is bounded
by `Nv` and `α`-Hölder with constant `Nv` on the larger polydisc `polydisc 0 R ⊇ polydisc 0 r`,
then `u * v` is bounded by `Nu * Nv` and is `α`-Hölder with constant `2 * Nu * Nv` on `ℂⁿ`. -/
private lemma mul_pointwise_bound {n : ℕ} {α : ℝ} {r R : Fin n → ℝ}
    (hsub : polydisc 0 r ⊆ polydisc 0 R)
    {u v : (Fin n → ℂ) → ℂ} (hsupp : ∀ z, z ∉ polydisc 0 r → u z = 0)
    {Nu Nv : ℝ} (hNu0 : 0 ≤ Nu) (hNv0 : 0 ≤ Nv)
    (hu : ∀ z, ‖u z‖ ≤ Nu)
    (huα : ∀ x y, x ≠ y → ‖u x - u y‖ ≤ Nu * ‖x - y‖ ^ α)
    (hv : ∀ z ∈ polydisc 0 R, ‖v z‖ ≤ Nv)
    (hvα : ∀ x ∈ polydisc 0 R, ∀ y ∈ polydisc 0 R, x ≠ y →
      ‖v x - v y‖ ≤ Nv * ‖x - y‖ ^ α) :
    (∀ z, ‖u z * v z‖ ≤ Nu * Nv) ∧
    (∀ x y, x ≠ y → ‖u x * v x - u y * v y‖ ≤ 2 * Nu * Nv * ‖x - y‖ ^ α) := by
  constructor
  · intro z
    by_cases hz : z ∈ polydisc 0 R
    · rw [norm_mul]
      exact mul_le_mul (hu z) (hv z hz) (norm_nonneg _) hNu0
    · have hzr : z ∉ polydisc 0 r := fun h => hz (hsub h)
      rw [hsupp z hzr, zero_mul, norm_zero]
      exact mul_nonneg hNu0 hNv0
  · intro x y hxy
    have hdpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    have hdnn : 0 ≤ ‖x - y‖ ^ α := le_of_lt hdpos
    by_cases hx : x ∈ polydisc 0 r
    · have hx' : x ∈ polydisc 0 R := hsub hx
      by_cases hy : y ∈ polydisc 0 r
      · have hy' : y ∈ polydisc 0 R := hsub hy
        have hsplit : u x * v x - u y * v y = u x * (v x - v y) + (u x - u y) * v y := by ring
        rw [hsplit]
        calc ‖u x * (v x - v y) + (u x - u y) * v y‖
            ≤ ‖u x * (v x - v y)‖ + ‖(u x - u y) * v y‖ := norm_add_le _ _
          _ = ‖u x‖ * ‖v x - v y‖ + ‖u x - u y‖ * ‖v y‖ := by rw [norm_mul, norm_mul]
          _ ≤ Nu * (Nv * ‖x - y‖ ^ α) + (Nu * ‖x - y‖ ^ α) * Nv :=
              add_le_add (mul_le_mul (hu x) (hvα x hx' y hy' hxy) (norm_nonneg _) hNu0)
                (mul_le_mul (huα x y hxy) (hv y hy') (norm_nonneg _) (mul_nonneg hNu0 hdnn))
          _ = 2 * Nu * Nv * ‖x - y‖ ^ α := by ring
      · have hy0 : u y = 0 := hsupp y hy
        have hux : ‖u x‖ ≤ Nu * ‖x - y‖ ^ α := by
          have h := huα x y hxy
          rwa [hy0, sub_zero] at h
        rw [hy0, zero_mul, sub_zero, norm_mul]
        calc ‖u x‖ * ‖v x‖
            ≤ (Nu * ‖x - y‖ ^ α) * Nv :=
              mul_le_mul hux (hv x hx') (norm_nonneg _) (mul_nonneg hNu0 hdnn)
          _ = Nu * Nv * ‖x - y‖ ^ α := by ring
          _ ≤ 2 * Nu * Nv * ‖x - y‖ ^ α := by
              have hnn : 0 ≤ Nu * Nv * ‖x - y‖ ^ α := mul_nonneg (mul_nonneg hNu0 hNv0) hdnn
              linarith
    · have hx0 : u x = 0 := hsupp x hx
      by_cases hy : y ∈ polydisc 0 r
      · have hy' : y ∈ polydisc 0 R := hsub hy
        have huy : ‖u y‖ ≤ Nu * ‖x - y‖ ^ α := by
          have h := huα x y hxy
          rwa [hx0, zero_sub, norm_neg] at h
        rw [hx0, zero_mul, zero_sub, norm_neg, norm_mul]
        calc ‖u y‖ * ‖v y‖
            ≤ (Nu * ‖x - y‖ ^ α) * Nv :=
              mul_le_mul huy (hv y hy') (norm_nonneg _) (mul_nonneg hNu0 hdnn)
          _ = Nu * Nv * ‖x - y‖ ^ α := by ring
          _ ≤ 2 * Nu * Nv * ‖x - y‖ ^ α := by
              have hnn : 0 ≤ Nu * Nv * ‖x - y‖ ^ α := mul_nonneg (mul_nonneg hNu0 hNv0) hdnn
              linarith
      · have hy0 : u y = 0 := hsupp y hy
        rw [hx0, hy0, zero_mul, zero_mul, sub_zero, norm_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hNu0) hNv0) hdnn

/-! ## Subadditivity of `iDN 0` and `hSN 0` (no differentiability needed) -/

private lemma iDN_zero_add_le {n : ℕ} (φ ψ : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.Holder.iDN 0 (φ + ψ) Ω
      ≤ Work.CR.Flat.Holder.iDN 0 φ Ω + Work.CR.Flat.Holder.iDN 0 ψ Ω := by
  rw [Work.CR.Flat.Holder.iDN_zero_deriv, Work.CR.Flat.Holder.iDN_zero_deriv,
    Work.CR.Flat.Holder.iDN_zero_deriv]
  refine iSup₂_le fun x hx => ?_
  rw [Pi.add_apply]
  calc ENNReal.ofReal ‖φ x + ψ x‖ ≤ ENNReal.ofReal (‖φ x‖ + ‖ψ x‖) :=
        ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ = ENNReal.ofReal ‖φ x‖ + ENNReal.ofReal ‖ψ x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖φ x‖) + (⨆ x ∈ Ω, ENNReal.ofReal ‖ψ x‖) :=
        add_le_add (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)

private lemma iDN_zero_sub_le {n : ℕ} (φ ψ : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.Holder.iDN 0 (φ - ψ) Ω
      ≤ Work.CR.Flat.Holder.iDN 0 φ Ω + Work.CR.Flat.Holder.iDN 0 ψ Ω := by
  rw [Work.CR.Flat.Holder.iDN_zero_deriv, Work.CR.Flat.Holder.iDN_zero_deriv,
    Work.CR.Flat.Holder.iDN_zero_deriv]
  refine iSup₂_le fun x hx => ?_
  rw [Pi.sub_apply]
  calc ENNReal.ofReal ‖φ x - ψ x‖ ≤ ENNReal.ofReal (‖φ x‖ + ‖ψ x‖) :=
        ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
    _ = ENNReal.ofReal ‖φ x‖ + ENNReal.ofReal ‖ψ x‖ :=
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
    _ ≤ (⨆ x ∈ Ω, ENNReal.ofReal ‖φ x‖) + (⨆ x ∈ Ω, ENNReal.ofReal ‖ψ x‖) :=
        add_le_add (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)

private lemma hSN_zero_add_le {n : ℕ} {α : ℝ} (φ ψ : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.Holder.hSN 0 α (φ + ψ) Ω
      ≤ Work.CR.Flat.Holder.hSN 0 α φ Ω + Work.CR.Flat.Holder.hSN 0 α ψ Ω := by
  rw [Work.CR.Flat.Holder.hSN_zero_deriv, Work.CR.Flat.Holder.hSN_zero_deriv,
    Work.CR.Flat.Holder.hSN_zero_deriv]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have heq : (φ + ψ) x - (φ + ψ) y = (φ x - φ y) + (ψ x - ψ y) := by
    simp only [Pi.add_apply]; abel
  rw [heq]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  calc ENNReal.ofReal (‖(φ x - φ y) + (ψ x - ψ y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((‖φ x - φ y‖ + ‖ψ x - ψ y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_add_le _ _) hd)
    _ = ENNReal.ofReal
          (‖φ x - φ y‖ / ‖x - y‖ ^ α + ‖ψ x - ψ y‖ / ‖x - y‖ ^ α) := by rw [add_div]
    _ = ENNReal.ofReal (‖φ x - φ y‖ / ‖x - y‖ ^ α)
        + ENNReal.ofReal (‖ψ x - ψ y‖ / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)
    _ ≤ (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖φ x - φ y‖ / ‖x - y‖ ^ α))
        + (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖ψ x - ψ y‖ / ‖x - y‖ ^ α)) :=
        add_le_add (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
          (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))

private lemma hSN_zero_sub_le {n : ℕ} {α : ℝ} (φ ψ : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.Holder.hSN 0 α (φ - ψ) Ω
      ≤ Work.CR.Flat.Holder.hSN 0 α φ Ω + Work.CR.Flat.Holder.hSN 0 α ψ Ω := by
  rw [Work.CR.Flat.Holder.hSN_zero_deriv, Work.CR.Flat.Holder.hSN_zero_deriv,
    Work.CR.Flat.Holder.hSN_zero_deriv]
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have heq : (φ - ψ) x - (φ - ψ) y = (φ x - φ y) - (ψ x - ψ y) := by
    simp only [Pi.sub_apply]; abel
  rw [heq]
  have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  calc ENNReal.ofReal (‖(φ x - φ y) - (ψ x - ψ y)‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal ((‖φ x - φ y‖ + ‖ψ x - ψ y‖) / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_sub_le _ _) hd)
    _ = ENNReal.ofReal
          (‖φ x - φ y‖ / ‖x - y‖ ^ α + ‖ψ x - ψ y‖ / ‖x - y‖ ^ α) := by rw [add_div]
    _ = ENNReal.ofReal (‖φ x - φ y‖ / ‖x - y‖ ^ α)
        + ENNReal.ofReal (‖ψ x - ψ y‖ / ‖x - y‖ ^ α) :=
        ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)
    _ ≤ (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖φ x - φ y‖ / ‖x - y‖ ^ α))
        + (⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y), ENNReal.ofReal (‖ψ x - ψ y‖ / ‖x - y‖ ^ α)) :=
        add_le_add (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
          (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))

/-! ## The main estimate -/

theorem bmH_norm_le_expl {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {r R : Fin n → ℝ} (hrR : ∀ j, r j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 r)
    {Nχ : ℝ} (hNχ : 0 < Nχ)
    (hχbar : ∀ (a : Fin n),
      Work.CR.Flat.holderNorm 0 α (fun w => Work.CR.Flat.dbarCoord a χ w) Set.univ
        ≤ ENNReal.ofReal Nχ) :
    ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ (0 : ℕ∞) (η i l) (Work.CR.Flat.polydisc 0 R)) → ∀ j l i : Fin n,
        Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
          ≤ ENNReal.ofReal (12 * (Nχ + 1)) * ∑ a : Fin n, ∑ b : Fin n,
              Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 R) := by
  intro η hη j l i
  set S : ℝ≥0∞ := ∑ a : Fin n, ∑ b : Fin n,
      Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 R) with hS
  by_cases hStop : S = ⊤
  · rw [hStop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  · have hsub : Work.CR.Flat.polydisc 0 r ⊆ Work.CR.Flat.polydisc 0 R :=
      Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hrR j))
    set Nv : Fin n → Fin n → ℝ :=
      fun c d => (Work.CR.Flat.holderNorm 0 α (η c d) (Work.CR.Flat.polydisc 0 R)).toReal
      with hNv
    have hHcd_le : ∀ c d : Fin n,
        Work.CR.Flat.holderNorm 0 α (η c d) (Work.CR.Flat.polydisc 0 R) ≤ S := by
      intro c d
      rw [hS]
      refine le_trans (Finset.single_le_sum
        (f := fun b => Work.CR.Flat.holderNorm 0 α (η c b) (Work.CR.Flat.polydisc 0 R))
        (fun b _ => bot_le) (Finset.mem_univ d)) ?_
      exact Finset.single_le_sum
        (f := fun a => ∑ b, Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 R))
        (fun a _ => Finset.sum_nonneg fun b _ => bot_le) (Finset.mem_univ c)
    have hHcd_ne : ∀ c d : Fin n,
        Work.CR.Flat.holderNorm 0 α (η c d) (Work.CR.Flat.polydisc 0 R) ≠ ⊤ :=
      fun c d => ne_top_of_le_ne_top hStop (hHcd_le c d)
    have hNv_ofReal : ∀ c d : Fin n, ENNReal.ofReal (Nv c d)
        = Work.CR.Flat.holderNorm 0 α (η c d) (Work.CR.Flat.polydisc 0 R) :=
      fun c d => ENNReal.ofReal_toReal (hHcd_ne c d)
    have hNv0 : ∀ c d : Fin n, 0 ≤ Nv c d := fun c d => ENNReal.toReal_nonneg
    have hNχ0 : 0 ≤ Nχ := le_of_lt hNχ
    -- pointwise bounds for each of the three products
    have hbnd : ∀ a : Fin n, ∀ c d : Fin n,
        (∀ z, ‖Work.CR.Flat.dbarCoord a χ z * η c d z‖ ≤ Nχ * Nv c d) ∧
        (∀ x y, x ≠ y → ‖Work.CR.Flat.dbarCoord a χ x * η c d x
            - Work.CR.Flat.dbarCoord a χ y * η c d y‖
          ≤ 2 * Nχ * Nv c d * ‖x - y‖ ^ α) := by
      intro a c d
      exact mul_pointwise_bound (α := α) hsub
        (fun z hz => dbarCoord_eq_zero_of_tsupport_subset htsupp a hz) hNχ0 (hNv0 c d)
        (fun z => sup_le_of_holderNorm hNχ0 (hχbar a) z (mem_univ z))
        (fun x y hxy => sub_le_of_holderNorm hNχ0 (hχbar a) x (mem_univ x) y (mem_univ y) hxy)
        (fun z hz => sup_le_of_holderNorm (hNv0 c d) (le_of_eq (hNv_ofReal c d).symm) z hz)
        (fun x hx y hy hxy =>
          sub_le_of_holderNorm (hNv0 c d) (le_of_eq (hNv_ofReal c d).symm) x hx y hy hxy)
    have hiDN : ∀ a : Fin n, ∀ c d : Fin n,
        Work.CR.Flat.Holder.iDN 0 (fun w => Work.CR.Flat.dbarCoord a χ w * η c d w) Set.univ
          ≤ ENNReal.ofReal (Nχ * Nv c d) := by
      intro a c d
      rw [Work.CR.Flat.Holder.iDN_zero_deriv]
      exact iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal ((hbnd a c d).1 z)
    have hhSN : ∀ a : Fin n, ∀ c d : Fin n,
        Work.CR.Flat.Holder.hSN 0 α (fun w => Work.CR.Flat.dbarCoord a χ w * η c d w) Set.univ
          ≤ ENNReal.ofReal (2 * Nχ * Nv c d) := by
      intro a c d
      rw [Work.CR.Flat.Holder.hSN_zero_deriv]
      refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
      have hdpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hdpos).mpr ((hbnd a c d).2 x y hxy))
    have hF_eq : (fun w => Work.NN.Core.bmH χ η j l i w)
        = (fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
          + (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
          - (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) := by
      funext w
      simp only [Work.NN.Core.bmH, Pi.add_apply, Pi.sub_apply]
    have hI : Work.CR.Flat.Holder.iDN 0 (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
        ≤ ENNReal.ofReal (Nχ * (Nv j l + Nv l i + Nv j i)) := by
      rw [hF_eq]
      calc Work.CR.Flat.Holder.iDN 0
            ((fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
              + (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
              - (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w)) Set.univ
          ≤ Work.CR.Flat.Holder.iDN 0
              ((fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
                + (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)) Set.univ
            + Work.CR.Flat.Holder.iDN 0
                (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) Set.univ :=
            iDN_zero_sub_le _ _ _
        _ ≤ (Work.CR.Flat.Holder.iDN 0
                (fun w => Work.CR.Flat.dbarCoord i χ w * η j l w) Set.univ
              + Work.CR.Flat.Holder.iDN 0
                (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w) Set.univ)
            + Work.CR.Flat.Holder.iDN 0
                (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) Set.univ :=
            add_le_add (iDN_zero_add_le _ _ _) le_rfl
        _ ≤ (ENNReal.ofReal (Nχ * Nv j l) + ENNReal.ofReal (Nχ * Nv l i))
            + ENNReal.ofReal (Nχ * Nv j i) :=
            add_le_add (add_le_add (hiDN i j l) (hiDN j l i)) (hiDN l j i)
        _ = ENNReal.ofReal (Nχ * (Nv j l + Nv l i + Nv j i)) := by
            rw [← ENNReal.ofReal_add (mul_nonneg hNχ0 (hNv0 j l)) (mul_nonneg hNχ0 (hNv0 l i)),
              ← ENNReal.ofReal_add
                (add_nonneg (mul_nonneg hNχ0 (hNv0 j l)) (mul_nonneg hNχ0 (hNv0 l i)))
                (mul_nonneg hNχ0 (hNv0 j i))]
            congr 1
            ring
    have hH : Work.CR.Flat.Holder.hSN 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
        ≤ ENNReal.ofReal (2 * Nχ * (Nv j l + Nv l i + Nv j i)) := by
      rw [hF_eq]
      calc Work.CR.Flat.Holder.hSN 0 α
            ((fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
              + (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)
              - (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w)) Set.univ
          ≤ Work.CR.Flat.Holder.hSN 0 α
              ((fun w => Work.CR.Flat.dbarCoord i χ w * η j l w)
                + (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w)) Set.univ
            + Work.CR.Flat.Holder.hSN 0 α
                (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) Set.univ :=
            hSN_zero_sub_le _ _ _
        _ ≤ (Work.CR.Flat.Holder.hSN 0 α
                (fun w => Work.CR.Flat.dbarCoord i χ w * η j l w) Set.univ
              + Work.CR.Flat.Holder.hSN 0 α
                (fun w => Work.CR.Flat.dbarCoord j χ w * η l i w) Set.univ)
            + Work.CR.Flat.Holder.hSN 0 α
                (fun w => Work.CR.Flat.dbarCoord l χ w * η j i w) Set.univ :=
            add_le_add (hSN_zero_add_le _ _ _) le_rfl
        _ ≤ (ENNReal.ofReal (2 * Nχ * Nv j l) + ENNReal.ofReal (2 * Nχ * Nv l i))
            + ENNReal.ofReal (2 * Nχ * Nv j i) :=
            add_le_add (add_le_add (hhSN i j l) (hhSN j l i)) (hhSN l j i)
        _ = ENNReal.ofReal (2 * Nχ * (Nv j l + Nv l i + Nv j i)) := by
            rw [← ENNReal.ofReal_add
                (mul_nonneg (mul_nonneg (by norm_num) hNχ0) (hNv0 j l))
                (mul_nonneg (mul_nonneg (by norm_num) hNχ0) (hNv0 l i)),
              ← ENNReal.ofReal_add
                (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hNχ0) (hNv0 j l))
                  (mul_nonneg (mul_nonneg (by norm_num) hNχ0) (hNv0 l i)))
                (mul_nonneg (mul_nonneg (by norm_num) hNχ0) (hNv0 j i))]
            congr 1
            ring
    -- the final bookkeeping
    have hNv_le : ∀ c d : Fin n, Nv c d ≤ S.toReal := fun c d =>
      ENNReal.toReal_mono hStop (hHcd_le c d)
    have hSnn : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    have hSsum : 0 ≤ Nv j l + Nv l i + Nv j i :=
      add_nonneg (add_nonneg (hNv0 j l) (hNv0 l i)) (hNv0 j i)
    have hreal : 3 * Nχ * (Nv j l + Nv l i + Nv j i) ≤ 12 * (Nχ + 1) * S.toReal := by
      have h1 : Nv j l + Nv l i + Nv j i ≤ 3 * S.toReal := by
        have a := hNv_le j l
        have b := hNv_le l i
        have c := hNv_le j i
        linarith
      have h2 : 3 * Nχ * (Nv j l + Nv l i + Nv j i) ≤ 3 * Nχ * (3 * S.toReal) :=
        mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 3 * Nχ)
      have h3 : 3 * Nχ * (3 * S.toReal) ≤ 12 * (Nχ + 1) * S.toReal := by nlinarith
      linarith
    rw [Work.CR.Flat.Holder.holderNorm_zero_eq]
    refine le_trans (add_le_add hI hH) ?_
    calc ENNReal.ofReal (Nχ * (Nv j l + Nv l i + Nv j i))
          + ENNReal.ofReal (2 * Nχ * (Nv j l + Nv l i + Nv j i))
        = ENNReal.ofReal (3 * Nχ * (Nv j l + Nv l i + Nv j i)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg hNχ0 hSsum)
            (mul_nonneg (mul_nonneg (by norm_num) hNχ0) hSsum)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (12 * (Nχ + 1)) * S := by
          rw [(ENNReal.ofReal_toReal hStop).symm]
          calc ENNReal.ofReal (3 * Nχ * (Nv j l + Nv l i + Nv j i))
              ≤ ENNReal.ofReal (12 * (Nχ + 1) * S.toReal) := ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal (12 * (Nχ + 1)) * ENNReal.ofReal S.toReal := by
                rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 12 * (Nχ + 1))]

end

end Work.NN.Newton.FTedat
