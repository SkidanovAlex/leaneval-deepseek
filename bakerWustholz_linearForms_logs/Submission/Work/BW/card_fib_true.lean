import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.torPart_image_filter_degBox

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-- `fibImg` splits as the number of possible values of `b 0` times the number of classes of the
torus part realized in the box: `b 0` and the exponents `bᵢ`, `i ≥ 1`, vary independently over
the exponent box `∏ᵢ [0, dᵢ]`, and the class `clsOf N ρ M (torPart b)` depends only on the
latter.  Note that the `b 0 = 0` slice already realizes every class. -/
private theorem fibImg_eq_succ_mul_clsImg {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ)
    (M : Fin ρ → Fin N → ℤ) :
    fibImg N ρ d M = (d 0 + 1) * clsImg N ρ d M := by
  classical
  unfold fibImg clsImg
  have hprod : (degBox N d).image (fun b => (b 0, clsOf N ρ M (torPart b)))
      = (Finset.range (d 0 + 1)) ×ˢ
          (((degBox N d).filter (fun b => b 0 = 0)).image
            (fun b => clsOf N ρ M (torPart b))) := by
    ext p
    rw [Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_range]
        have h := (mem_degBox d b).mp hb 0
        omega
      · rw [Finset.mem_image]
        refine ⟨Function.update b 0 0, ?_, ?_⟩
        · rw [Finset.mem_filter]
          constructor
          · rw [mem_degBox]
            intro i
            rw [Function.update_apply]
            by_cases hi : i = 0
            · subst hi
              rw [ite_eq_left rfl]
              exact Nat.zero_le _
            · rw [ite_eq_right hi]
              exact (mem_degBox d b).mp hb i
          · rw [Function.update_apply, ite_eq_left rfl]
        · have htor : torPart (Function.update b 0 0) = torPart b := by
            funext i
            show ((Function.update b 0 0 i.succ : ℕ) : ℤ) = ((b i.succ : ℕ) : ℤ)
            rw [Function.update_of_ne (Fin.succ_ne_zero i) (0 : ℕ) b]
          exact congrArg (clsOf N ρ M) htor
    · rintro ⟨ha, hb2⟩
      rw [Finset.mem_image] at hb2
      obtain ⟨b, hb, hbc⟩ := hb2
      rw [Finset.mem_filter] at hb
      obtain ⟨hbdeg, _⟩ := hb
      rw [Finset.mem_range] at ha
      refine ⟨Function.update b 0 p.1, ?_, ?_⟩
      · rw [mem_degBox]
        intro i
        rw [Function.update_apply]
        by_cases hi : i = 0
        · subst hi
          rw [ite_eq_left rfl]
          omega
        · rw [ite_eq_right hi]
          exact (mem_degBox d b).mp hbdeg i
      · refine Prod.ext ?_ ?_
        · rw [Function.update_apply, ite_eq_left rfl]
        · have htor : torPart (Function.update b 0 p.1) = torPart b := by
            funext i
            show ((Function.update b 0 p.1 i.succ : ℕ) : ℤ) = ((b i.succ : ℕ) : ℤ)
            rw [Function.update_of_ne (Fin.succ_ne_zero i) p.1 b]
          rw [htor, hbc]
  rw [hprod, Finset.card_product, Finset.card_range]

/-- Counting the classes of the torus part of the exponent box mod `𝒵`: the exponent vectors
`b ∈ degBox N d` with `b 0 = 0` correspond bijectively to the lattice box `∏ᵢ [0, d_{i+1}]`,
whose class count is `boxClassCount N ρ M (fun i => d i.succ)`. -/
private theorem clsImg_eq_boxClassCount_aux {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ)
    (M : Fin ρ → Fin N → ℤ) :
    clsImg N ρ d M = boxClassCount N ρ M (fun i => d i.succ) := by
  classical
  unfold clsImg boxClassCount
  have h1 : (((degBox N d).filter (fun b => b 0 = 0)).image
        (fun b => clsOf N ρ M (torPart b)))
      = ((((degBox N d).filter (fun b => b 0 = 0)).image (fun b => torPart b))).image
          (clsOf N ρ M) := by
    rw [Finset.image_image]
    rfl
  have h2 : ((((degBox N d).filter (fun b => b 0 = 0)).image (fun b => torPart b))).image
        (clsOf N ρ M)
      = (boxPts N (fun i => d i.succ)).image
          (fun b => (Submodule.Quotient.mk b : (Fin N → ℤ) ⧸ rowLat N ρ M)) := by
    rw [torPart_image_filter_degBox d]
    rfl
  rw [h1, h2]

/-- Counting the fibers of the exponent box: the number of pairs `(b 0, class of the torus part mod 𝒵)` realized by exponent vectors `b` with `bᵢ ≤ dᵢ` is `(d₀+1) · boxClassCount`.

(`fibImg` is the cardinality of the image of `degBox N d` under `b ↦ (b 0, clsOf N ρ M (torPart b))`; the classes of the torus part are exactly the classes of the box `∏ᵢ[0,d_{i+1}]` counted by `boxClassCount`, and `b 0` ranges freely over `0,…,d 0`.) -/
theorem card_fib_true {N ρ : ℕ} (d : Fin (N + 1) →₀ ℕ) (M : Fin ρ → Fin N → ℤ) :
    fibImg N ρ d M = (d 0 + 1) * boxClassCount N ρ M (fun i => d i.succ) := by
  rw [fibImg_eq_succ_mul_clsImg, clsImg_eq_boxClassCount_aux]

end Work.BW
