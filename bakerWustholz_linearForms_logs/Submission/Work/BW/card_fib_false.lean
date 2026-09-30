import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.boxPts_eq_Icc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Membership in the exponent box `degBox N d`: the exponent vectors with `bᵢ ≤ dᵢ`. -/
lemma mem_degBox {N : ℕ} {d : Fin (N + 1) →₀ ℕ} {b : Fin (N + 1) → ℕ} :
    b ∈ degBox N d ↔ ∀ i, b i ≤ d i := by
  unfold degBox
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, hc, hcb⟩ i
    have h1 : c i (Finset.mem_univ i) ∈ Finset.range (d i + 1) :=
      (Finset.mem_pi.mp hc) i (Finset.mem_univ i)
    rw [Finset.mem_range] at h1
    rw [← congr_fun hcb i]
    exact Nat.lt_succ_iff.mp h1
  · intro hb
    refine ⟨fun i _ => b i, ?_, rfl⟩
    rw [Finset.mem_pi]
    intro i _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact hb i

/-- Membership in the box `boxPts N m`: the lattice points whose coordinates lie in `[0, mᵢ]`. -/
lemma mem_boxPts {N : ℕ} {m : Fin N → ℕ} {x : Fin N → ℤ} :
    x ∈ boxPts N m ↔ ∀ i, 0 ≤ x i ∧ x i ≤ (m i : ℤ) := by
  rw [boxPts_eq_Icc, Finset.mem_Icc]
  constructor
  · intro h i
    exact ⟨h.1 i, h.2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

/-- The exponent vectors with `b 0 = 0` and `bᵢ ≤ dᵢ`, read on their torus part `(b_{i+1})`,
are exactly the lattice points of the box `∏ᵢ [0, d_{i+1}]`. -/
lemma image_torPart_filter_degBox (N : ℕ) (d : Fin (N + 1) →₀ ℕ) :
    ((degBox N d).filter (fun b => b 0 = 0)).image (fun b => torPart b) =
      boxPts N (fun i => d i.succ) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, mem_boxPts]
  constructor
  · rintro ⟨b, ⟨hb, _⟩, hbx⟩ i
    rw [← hbx]
    show 0 ≤ (b i.succ : ℤ) ∧ (b i.succ : ℤ) ≤ (d i.succ : ℤ)
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (mem_degBox.mp hb) i.succ⟩
  · intro hx
    refine ⟨(Fin.cons 0 (fun i : Fin N => (x i).toNat) : Fin (N + 1) → ℕ), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_degBox, Fin.forall_fin_succ]
      exact ⟨by rw [Fin.cons_zero]; exact Nat.zero_le _, fun j => by
        rw [Fin.cons_succ]
        exact Int.toNat_le.mpr (hx j).2⟩
    · exact Fin.cons_zero _ _
    · funext i
      show ((Fin.cons (0 : ℕ) (fun i : Fin N => (x i).toNat) : Fin (N + 1) → ℕ) i.succ : ℤ) = x i
      rw [Fin.cons_succ]
      exact Int.toNat_of_nonneg (hx i).1

/-- Counting the classes of the torus box as exponent vectors: the number of classes modulo `𝒵` of the points `(bᵢ)_{i≥1}` with `b 0 = 0` and `bᵢ ≤ dᵢ` is `boxClassCount N ρ M (fun i => d i.succ)`.

(`clsImg` is the cardinality of the image of `{b ∈ degBox N d | b 0 = 0}` under `b ↦ clsOf N ρ M (torPart b)`; these exponent vectors correspond bijectively to the box points `∏ᵢ[0,d_{i+1}]` of `boxPts`, whose class count is `boxClassCount`.) -/
theorem card_fib_false {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ) :
    clsImg N ρ d M = boxClassCount N ρ M (fun i => d i.succ) := by
  classical
  have h : ((degBox N d).filter (fun b => b 0 = 0)).image
        (fun b => (Submodule.Quotient.mk (torPart b) : (Fin N → ℤ) ⧸ rowLat N ρ M)) =
      (boxPts N (fun i => d i.succ)).image
        (fun v => (Submodule.Quotient.mk v : (Fin N → ℤ) ⧸ rowLat N ρ M)) := by
    rw [← image_torPart_filter_degBox N d, Finset.image_image]
    apply Finset.image_congr
    intro b _
    rfl
  simp only [clsImg, boxClassCount, clsOf]
  rw [h]

end Work.BW
