import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASRulV2M.sat_mem_gen
import Submission.Work.MotAS.ASRulV2M.reduce_quad
import Submission.Work.MotAS.ASRulV2M.ann_eq_gen
import Submission.Work.MotAS.ASRulV2M.Nn_dvd_gen
import Submission.Work.MotAS.ASRulV2M.sat_mem13
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.Reflect.PolyId

/-!
# `Work.MotAS.ASRulV2M.D0_regular_gen`

`D₀ := ASZGC.D0 a b g` (the `X 0`-coefficient of the graph element of the AS residual chart ideal
`Z := ZIAS a b g`) is a non-zero-divisor modulo `Z`, for every field `K` of characteristic `5` and
`a b g : K` with `a² - ab - b² ≠ 0` and `g ∉ ℘(K)`.

**The statement is TRUE** (`Z : D₀ = Z`; verified for all admissible `(a,b,g) ∈ 𝔽₅³` and more).

## The proof design (assembly = `D0_regular_of` below)

Write `β := aszQuBeta a b ≠ 0` (from `ha`), `l := C (β²)⁻¹ · aszQuLt`,
`A := C (β²)⁻¹ · aszQuAt`, `e := X 0^2 + rename l · X 0 + rename A ∈ Z` (`aszQuad_mem`),
`G := rename D₀ · X 0 + rename R₀ ∈ Z` (`D0_graph_mem`), `P := ASZElim.P a b g`.

1. `reduce_quad` reduces an arbitrary `y` modulo `(e)` to `u = rename α + rename β' · X 0`
   (`e` is monic in `X 0`, so this is polynomial division).
2. `rename (D₀ α - β' R₀) = rename D₀ · u - rename β' · G ∈ Z`; by the elimination
   `aszElim_dvd_of_le_sat` (i.e. `Z ∩ K[X₁,X₂] = (P)`, from the saturation `SatAS`) this gives
   `P ∣ D₀ α - β' R₀`.
3. The annihilator input `ann_eq_gen` (`(P,D₀) : (R₀) = (P,D₀,R₀)`) gives
   `β' = c₁ P + c₂ D₀ + c₃ R₀`, and the determinant identity `det_identity_of`
   (`R₀² - l R₀ D₀ + A D₀² ∈ (P)`) gives `P ∣ α - (c₂ R₀ + c₃ (l R₀ - A D₀))` after cancelling the
   non-zero-divisor `D̄₀` in `A = K[X₁,X₂]/(P)` (`P` prime).  The explicit identity

     `u = cW · P̃ + c₂ G + c₁ (X 0 · P̃) + (c₃ (l + X 0)) G - (c₃ D̃₀) e`

   (`ring`, using `β' = c₁ P + c₂ D₀ + c₃ R₀` and `α = P cW + (c₂ R₀ + c₃ (l R₀ - A D₀))`) then
   exhibits `u ∈ (P̃, e, G) ⊆ Z`.
4. `y = u + (y - u) ∈ Z`.

The saturation memberships `zcubAS a b g k ∈ SatAS` for `k = 0, 2, 4` are in `sat_mem_gen`; for
`k = 1, 3` they are `zcubAS_mem_sat_13` (which needs `Nn_dvd_gen`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotAS.ASRulV2M

open MvPolynomial

/-- Extraction of an explicit representation from membership in a three-generator ideal. -/
lemma mem_span_three_ideal {R : Type*} [CommRing R] {a b c x : R}
    (h : x ∈ Ideal.span ({a, b, c} : Set R)) :
    ∃ p q r : R, x = p * a + q * b + r * c := by
  have h₁ : x ∈ Submodule.span R (Set.insert a (Set.insert b (Set.singleton c))) := h
  obtain ⟨p, z₁, hz₁, hx⟩ := Submodule.mem_span_insert.mp h₁
  obtain ⟨q, z₂, hz₂, hz₁'⟩ := Submodule.mem_span_insert.mp hz₁
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hz₂
  refine ⟨p, q, r, ?_⟩
  rw [hx, hz₁', ← hr]
  simp only [smul_eq_mul]
  first | refl_ring1 | ring

/-- **The assembly**: given the saturation `hZS : ZIAS a b g ≤ SatAS K a b g` and the annihilator
input `hann`, the graph coefficient `D₀` is a non-zero-divisor modulo `ZIAS a b g`. -/
theorem D0_regular_of (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g)
    (hZS : Work.MotAS.ZIAS a b g ≤ SatAS K a b g)
    (hann : ∀ s : MvPolynomial (Fin 2) K,
      (∃ u v : MvPolynomial (Fin 2) K,
        s * Work.MotAS.ASZGC.R0 a b g
          = u * Work.MotAS.ASZElim.P a b g + v * Work.MotAS.ASZGC.D0 a b g) →
      s ∈ Ideal.span {Work.MotAS.ASZElim.P a b g, Work.MotAS.ASZGC.D0 a b g,
        Work.MotAS.ASZGC.R0 a b g}) :
    ∀ y : MvPolynomial (Fin 3) K,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) * y
        ∈ Work.MotAS.ZIAS a b g → y ∈ Work.MotAS.ZIAS a b g := by
  intro y hy
  set l : MvPolynomial (Fin 2) K :=
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuLt a b g with hl
  set A : MvPolynomial (Fin 2) K :=
    MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹ * Work.MotAS.aszQuAt a b g with hA
  set e3 : MvPolynomial (Fin 3) K :=
    MvPolynomial.X 0 ^ 2 + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A with he3def
  set G : MvPolynomial (Fin 3) K :=
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g) with hGdef
  have he3 : e3 ∈ Work.MotAS.ZIAS a b g := by
    have hl' : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l
        = MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuLt a b g) := by
      rw [hl, map_mul, MvPolynomial.rename_C]
    have hA' : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) A
        = MvPolynomial.C ((Work.MotAS.aszQuBeta a b) ^ 2)⁻¹
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.aszQuAt a b g) := by
      rw [hA, map_mul, MvPolynomial.rename_C]
    rw [he3def, hl', hA']
    exact aszQuad_mem K a b g ha
  have hPmem : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)
      ∈ Work.MotAS.ZIAS a b g := Work.MotAS.ASZElimMem K a b g ha hg
  have hGmem : G ∈ Work.MotAS.ZIAS a b g := by
    rw [hGdef]; exact D0_graph_mem K a b g
  obtain ⟨α, β, hαβ⟩ := reduce_quad l A y
  rw [← he3def] at hαβ
  have hαβZ : y - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)
      ∈ Work.MotAS.ZIAS a b g :=
    (Ideal.span_le.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact he3)) hαβ
  -- `D₀ α - β R₀ ∈ Z`
  have hmem : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
      (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g)
      ∈ Work.MotAS.ZIAS a b g := by
    have hkey : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)
        (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g)
        = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) * y
          - MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
              * (y - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
                + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0))
          - MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * G := by
      rw [hGdef]
      simp only [map_sub, map_mul]
      first | refl_ring1 | ring
    rw [hkey]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hy (Ideal.mul_mem_left _ _ hαβZ))
      (Ideal.mul_mem_left _ _ hGmem)
  obtain ⟨q, hq⟩ := aszElim_dvd_of_le_sat K a b g ha hg hZS
    (Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g) hmem
  -- the annihilator input
  have hβ : β ∈ Ideal.span {Work.MotAS.ASZElim.P a b g, Work.MotAS.ASZGC.D0 a b g,
      Work.MotAS.ASZGC.R0 a b g} := by
    refine hann β ⟨-q, α, ?_⟩
    linear_combination (norm := first | refl_ring1 | ring1) (-1) * hq
  obtain ⟨c1, c2, c3, hc⟩ := mem_span_three_ideal hβ
  set W : MvPolynomial (Fin 2) K := α - (c2 * Work.MotAS.ASZGC.R0 a b g
      + c3 * (l * Work.MotAS.ASZGC.R0 a b g - A * Work.MotAS.ASZGC.D0 a b g)) with hW
  have hαW : α = W + (c2 * Work.MotAS.ASZGC.R0 a b g
      + c3 * (l * Work.MotAS.ASZGC.R0 a b g - A * Work.MotAS.ASZGC.D0 a b g)) := by
    rw [hW]; ring
  -- `P ∣ W`
  have hWmem : Work.MotAS.ASZElim.P a b g ∣ W := by
    have hPprime : Prime (Work.MotAS.ASZElim.P a b g) :=
      (Work.MotAS.ASZElimP_irreducible K a b g ha hg).prime
    have hnotdvd : ¬ Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.D0 a b g :=
      Work.MotAS.ASZGC.not_dvd_D0 K a b g ha hg
    have hdet := det_identity_of K a b g ha hg hZS
    obtain ⟨d, hd⟩ := hdet
    have hd' : (Work.MotAS.ASZGC.R0 a b g) ^ 2
          - l * Work.MotAS.ASZGC.R0 a b g * Work.MotAS.ASZGC.D0 a b g
          + A * (Work.MotAS.ASZGC.D0 a b g) ^ 2
          = Work.MotAS.ASZElim.P a b g * d := by
      rw [hl, hA]; exact hd
    have hβc : β = c1 * Work.MotAS.ASZElim.P a b g + c2 * Work.MotAS.ASZGC.D0 a b g
        + c3 * Work.MotAS.ASZGC.R0 a b g := hc
    have hDW : Work.MotAS.ASZGC.D0 a b g * W
        = Work.MotAS.ASZElim.P a b g * (c1 * Work.MotAS.ASZGC.R0 a b g + q
          + c3 * d) := by
      have e1 : Work.MotAS.ASZGC.D0 a b g * α - β * Work.MotAS.ASZGC.R0 a b g
          = Work.MotAS.ASZElim.P a b g * q := hq
      have e2 : β - (c1 * Work.MotAS.ASZElim.P a b g + c2 * Work.MotAS.ASZGC.D0 a b g
          + c3 * Work.MotAS.ASZGC.R0 a b g) = 0 := by rw [hβc]; ring
      rw [hW]
      linear_combination (norm := first | refl_ring1 | ring1) e1 + Work.MotAS.ASZGC.R0 a b g * e2 + c3 * hd'
    exact (hPprime.dvd_mul.mp ⟨_, hDW⟩).resolve_left hnotdvd
  obtain ⟨cW, hcW⟩ := hWmem
  -- final algebra
  have hmem3 : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0
      ∈ Work.MotAS.ZIAS a b g := by
    have hαcW : α = Work.MotAS.ASZElim.P a b g * cW + (c2 * Work.MotAS.ASZGC.R0 a b g
        + c3 * (l * Work.MotAS.ASZGC.R0 a b g - A * Work.MotAS.ASZGC.D0 a b g)) := by
      rw [hαW, hcW]
    have hkey : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0
        = MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) cW
            * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g)
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c2 * G
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c1
              * (MvPolynomial.X 0
                * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZElim.P a b g))
          + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c3
              * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l + MvPolynomial.X 0) * G
          - MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c3
              * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)
              * e3 := by
      rw [hαcW, hc, hGdef, he3def]
      simp only [map_add, map_sub, map_mul, map_pow]
      first | refl_ring1 | ring
    rw [hkey]
    refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_) ?_
    · exact Ideal.mul_mem_left _ _ hPmem
    · exact Ideal.mul_mem_left _ _ hGmem
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ (MvPolynomial.X 0) hPmem)
    · exact Ideal.mul_mem_left _
        (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c3
          * (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) l + MvPolynomial.X 0)) hGmem
    · exact Ideal.mul_mem_left _
        (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) c3
          * MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) he3
  have hyeq : y = (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)
      + (y - (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) α
        + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) β * MvPolynomial.X 0)) := by ring
  rw [hyeq]
  exact Ideal.add_mem _ hmem3 hαβZ

theorem D0_regular_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    ∀ y : MvPolynomial (Fin 3) K,
      (MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g)) * y
        ∈ Work.MotAS.ZIAS a b g → y ∈ Work.MotAS.ZIAS a b g := by
  have hnn := Nn_dvd_gen K a b g ha hg
  have hm1 : ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 1
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} :=
    zcubAS_mem_sat_1_of K a b g hnn.2.1
  have hm3 : ∃ N : ℕ, (Work.MotC5N3.X2AuxInputs.D a b g) ^ N * Work.MotAS.zcubAS a b g 3
      ∈ Ideal.span {Work.MotC5N3.X2AuxInputs.Pemb a b g, Work.MotC5N3.X2AuxInputs.G a b g} :=
    zcubAS_mem_sat_3_of K a b g hnn.2.2.2.1
  have hgen : ∀ k : Fin 5, Work.MotAS.zcubAS a b g k ∈ SatAS K a b g := by
    intro k
    fin_cases k
    · exact Ideal.subset_span (zcubAS_mem_sat_0 K a b g)
    · exact Ideal.subset_span hm1
    · exact Ideal.subset_span (zcubAS_mem_sat_2 K a b g)
    · exact Ideal.subset_span hm3
    · exact Ideal.subset_span (zcubAS_mem_sat_4 K a b g)
  exact D0_regular_of K a b g ha hg (zias_le_sat_of K a b g hgen) (ann_eq_gen K a b g ha hg)

end Work.MotAS.ASRulV2M
