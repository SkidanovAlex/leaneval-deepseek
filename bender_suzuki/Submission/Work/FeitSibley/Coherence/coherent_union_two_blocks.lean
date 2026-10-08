import Mathlib
import Submission.Work.Coherence.Defs
import Submission.Work.Coherence.extend_of_gram
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.Coherence

open Work.Coherence

/-!
# Coherence of the union of two coherent blocks

`Work.FeitSibley.Coherence.coherent_union_two_blocks`: if `X` and `Y` are disjoint subsets of an
orthonormal set `S` of class functions on `H`, `τ` is a `ℤ`-linear map `ℤ[H → ℂ] → ℤ[G → ℂ]`
which agrees on `ℤ[X]⁰` with an isometry `σ` of `ℤ[X]` (with virtual-character values) and on
`ℤ[Y]⁰` with an isometry `ρ` of `ℤ[Y]` (with virtual-character values), the images of `X` and `Y`
are mutually orthogonal, all degrees in `X` are integral multiples of `deg x₀`, all degrees in `Y`
are integral multiples of `deg y₀`, `deg x₀ = a · deg y₀`, and `τ (x₀ - a·y₀) = σ x₀ - a·ρ y₀`,
then `X ∪ Y` is `τ`-coherent.

The proof constructs the candidate lift `φ := σ` on `X` and `ρ` on `Y`, verifies that `φ` has the
Gram matrix of `X ∪ Y` (using the two isometry hypotheses and the orthogonality of the images)
and that `φ` is compatible with `τ` on `ℤ[X ∪ Y]⁰` (the degree bookkeeping), and concludes with
`Work.Coherence.extend_of_gram`.
-/

/-- Sums over the subtype `↥(U ∪ V)` split into sums over `↥U` and `↥V` when `U` and `V` are
disjoint. -/
theorem sum_subtype_union {α M : Type*} [DecidableEq α] [AddCommMonoid M] {U V : Finset α}
    (hd : Disjoint U V) (F : α → M) :
    (∑ x : ↥(U ∪ V), F (x : α)) = (∑ x : ↥U, F (x : α)) + (∑ x : ↥V, F (x : α)) := by
  rw [Finset.univ_eq_attach (U ∪ V), Finset.univ_eq_attach U, Finset.univ_eq_attach V]
  rw [Finset.sum_attach, Finset.sum_attach, Finset.sum_attach]
  exact Finset.sum_union hd

theorem coherent_union_two_blocks {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]
    {S X Y : Finset (H → ℂ)} {τ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hS : Work.Coherence.Orthonormal S) (hXS : X ⊆ S) (hYS : Y ⊆ S) (hXY : Disjoint X Y)
    {σ ρ : (H → ℂ) →ₗ[ℤ] (G → ℂ)}
    (hσ0 : ∀ α ∈ Work.Coherence.ZSpan0 X, σ α = τ α) (hσ : Work.Coherence.IsometryOnAll X σ)
    (hσV : ∀ x ∈ X, Work.Coherence.IsVChar (σ x))
    (hρ0 : ∀ α ∈ Work.Coherence.ZSpan0 Y, ρ α = τ α) (hρ : Work.Coherence.IsometryOnAll Y ρ)
    (hρV : ∀ y ∈ Y, Work.Coherence.IsVChar (ρ y))
    (horth : ∀ x ∈ X, ∀ y ∈ Y, Work.Coherence.cfInner (σ x) (ρ y) = 0)
    {x₀ : H → ℂ} (hx₀ : x₀ ∈ X) {y₀ : H → ℂ} (hy₀ : y₀ ∈ Y) {a : ℕ}
    (hdegX : ∀ x ∈ X, ∃ k : ℤ, x 1 = (k : ℂ) * (x₀ 1))
    (hdegY : ∀ y ∈ Y, ∃ k : ℤ, y 1 = (k : ℂ) * (y₀ 1))
    (hax : (x₀ 1) = (a : ℂ) * (y₀ 1))
    (hrel : τ (x₀ - (a : ℂ) • y₀) = σ x₀ - (a : ℂ) • ρ y₀) :
    Work.Coherence.Coherent (X ∪ Y) τ := by
  classical
  -- the candidate lift: `σ` on `X`, `ρ` on `Y`
  let φ : (H → ℂ) → (G → ℂ) := fun v => if v ∈ X then σ v else ρ v
  have hφX : ∀ v ∈ X, φ v = σ v := fun v hv => by
    change (if v ∈ X then σ v else ρ v) = σ v
    rw [ite_eq_left hv]
  have hφY : ∀ v ∈ Y, φ v = ρ v := fun v hv => by
    change (if v ∈ X then σ v else ρ v) = ρ v
    rw [ite_eq_right (Finset.disjoint_right.mp hXY hv)]
  -- the Gram matrix of `φ` on `X ∪ Y`
  have hgram : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, cfInner (φ x) (φ y) = cfInner x y := by
    intro x hx y hy
    rcases Finset.mem_union.mp hx with hxX | hxY
    · rcases Finset.mem_union.mp hy with hyX | hyY
      · rw [hφX x hxX, hφX y hyX]
        exact hσ.inner_eq x (self_mem_zSpan hxX) y (self_mem_zSpan hyX)
      · rw [hφX x hxX, hφY y hyY, horth x hxX y hyY]
        have hne : x ≠ y := fun h => Finset.disjoint_left.mp hXY hxX (h.symm ▸ hyY)
        rw [hS x (hXS hxX) y (hYS hyY), ite_eq_right hne]
    · rw [hφY x hxY]
      rcases Finset.mem_union.mp hy with hyX | hyY
      · rw [hφX y hyX, cfInner_conj_symm, horth y hyX x hxY, map_zero]
        have hne : x ≠ y := fun h => Finset.disjoint_right.mp hXY hxY (h.symm ▸ hyX)
        rw [hS x (hYS hxY) y (hXS hyX), ite_eq_right hne]
      · rw [hφY y hyY]
        exact hρ.inner_eq x (self_mem_zSpan hxY) y (self_mem_zSpan hyY)
  -- compatibility with `τ` on the degree-zero lattice
  have hcompat : ∀ c : ↥(X ∪ Y) → ℤ,
      (∑ z : ↥(X ∪ Y), (c z : ℂ) • (z : H → ℂ)) 1 = 0 →
      ∑ z : ↥(X ∪ Y), (c z : ℂ) • φ (z : H → ℂ)
        = τ (∑ z : ↥(X ∪ Y), (c z : ℂ) • (z : H → ℂ)) := by
    intro c hc1
    let cA : (H → ℂ) → ℤ := fun v => if hv : v ∈ X ∪ Y then c ⟨v, hv⟩ else 0
    let cX : ↥X → ℤ := fun x => cA (x : H → ℂ)
    let cY : ↥Y → ℤ := fun y => cA (y : H → ℂ)
    let αX : H → ℂ := ∑ x : ↥X, (cX x : ℂ) • (x : H → ℂ)
    let αY : H → ℂ := ∑ y : ↥Y, (cY y : ℂ) • (y : H → ℂ)
    have hcA_apply : ∀ z : ↥(X ∪ Y), c z = cA (z : H → ℂ) := fun z => by
      show c z = (if hv : (z : H → ℂ) ∈ X ∪ Y then c ⟨z.1, hv⟩ else 0)
      rw [dite_eq_left z.2]
    have hmap : ∀ (f : (H → ℂ) →ₗ[ℤ] (G → ℂ)) (k : ℤ) (v : H → ℂ),
        f ((k : ℂ) • v) = (k : ℂ) • f v := fun f k v => by
      rw [Int.cast_smul_eq_zsmul ℂ k v, map_smul, Int.cast_smul_eq_zsmul ℂ k (f v)]
    have hmapNat : ∀ (f : (H → ℂ) →ₗ[ℤ] (G → ℂ)) (k : ℕ) (v : H → ℂ),
        f ((k : ℂ) • v) = (k : ℂ) • f v := fun f k v => by
      have h := hmap f (k : ℤ) v
      simpa using h
    -- the degree bookkeeping: `m`, `n` with `αX 1 = m · x₀ 1` and `αY 1 = n · y₀ 1`
    let kf : ↥X → ℤ := fun x => Classical.choose (hdegX (x : H → ℂ) x.2)
    have hkf_spec : ∀ x : ↥X, (x : H → ℂ) 1 = (kf x : ℂ) * (x₀ 1) :=
      fun x => Classical.choose_spec (hdegX (x : H → ℂ) x.2)
    let lf : ↥Y → ℤ := fun y => Classical.choose (hdegY (y : H → ℂ) y.2)
    have hlf_spec : ∀ y : ↥Y, (y : H → ℂ) 1 = (lf y : ℂ) * (y₀ 1) :=
      fun y => Classical.choose_spec (hdegY (y : H → ℂ) y.2)
    let m : ℤ := ∑ x : ↥X, cX x * kf x
    let n : ℤ := ∑ y : ↥Y, cY y * lf y
    have hmcast : (m : ℂ) = ∑ x : ↥X, (cX x : ℂ) * (kf x : ℂ) := by
      show ((∑ x : ↥X, cX x * kf x : ℤ) : ℂ) = _
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun x _ => by push_cast; ring
    have hncast : (n : ℂ) = ∑ y : ↥Y, (cY y : ℂ) * (lf y : ℂ) := by
      show ((∑ y : ↥Y, cY y * lf y : ℤ) : ℂ) = _
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun y _ => by push_cast; ring
    have hαX1 : αX 1 = (m : ℂ) * (x₀ 1) := by
      show (∑ x : ↥X, (cX x : ℂ) • (x : H → ℂ)) 1 = (m : ℂ) * (x₀ 1)
      rw [sum_coeff_apply, hmcast, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by rw [hkf_spec x]; ring
    have hαY1 : αY 1 = (n : ℂ) * (y₀ 1) := by
      show (∑ y : ↥Y, (cY y : ℂ) • (y : H → ℂ)) 1 = (n : ℂ) * (y₀ 1)
      rw [sum_coeff_apply, hncast, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by rw [hlf_spec y]; ring
    -- the split `α = αX + αY`
    have hαeq : (∑ z : ↥(X ∪ Y), (c z : ℂ) • (z : H → ℂ)) = αX + αY := by
      rw [Finset.sum_congr rfl (fun z _ => by rw [hcA_apply z])]
      show (∑ z : ↥(X ∪ Y), (cA (z : H → ℂ) : ℂ) • (z : H → ℂ)) = αX + αY
      rw [sum_subtype_union hXY (fun v : H → ℂ => (cA v : ℂ) • v)]
    have hαXαY1 : αX 1 + αY 1 = 0 := by
      have hh := hc1
      rw [hαeq, Pi.add_apply] at hh
      exact hh
    -- the degrees are integral multiples
    have hmany : ((m * (a : ℤ) + n : ℤ) : ℂ) * (y₀ 1) = 0 := by
      have h := hαXαY1
      rw [hαX1, hαY1, hax] at h
      have h2 : ((m : ℂ) * (a : ℂ) + (n : ℂ)) * (y₀ 1) = 0 := by
        linear_combination h
      rw [← h2]
      push_cast
      ring
    -- the two degree-zero corrections
    have huX : αX - (m : ℂ) • x₀ ∈ ZSpan0 X := by
      rw [mem_zSpan0]
      refine ⟨AddSubgroup.sub_mem _ (mem_zSpan.mpr ⟨cX, rfl⟩) ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul ℂ m x₀]
        exact AddSubgroup.zsmul_mem _ (self_mem_zSpan hx₀) m
      · rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hαX1, sub_self]
    have huY : αY - (n : ℂ) • y₀ ∈ ZSpan0 Y := by
      rw [mem_zSpan0]
      refine ⟨AddSubgroup.sub_mem _ (mem_zSpan.mpr ⟨cY, rfl⟩) ?_, ?_⟩
      · rw [Int.cast_smul_eq_zsmul ℂ n y₀]
        exact AddSubgroup.zsmul_mem _ (self_mem_zSpan hy₀) n
      · rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hαY1, sub_self]
    -- decompose `σ αX`, `ρ αY`, `τ αX`, `τ αY`
    have e1 : σ αX = τ (αX - (m : ℂ) • x₀) + (m : ℂ) • σ x₀ := by
      have hdec : αX = (αX - (m : ℂ) • x₀) + (m : ℂ) • x₀ := by abel
      have hh := congrArg σ hdec
      rw [map_add] at hh
      rw [hσ0 (αX - (m : ℂ) • x₀) huX, hmap σ m x₀] at hh
      exact hh
    have e2 : ρ αY = τ (αY - (n : ℂ) • y₀) + (n : ℂ) • ρ y₀ := by
      have hdec : αY = (αY - (n : ℂ) • y₀) + (n : ℂ) • y₀ := by abel
      have hh := congrArg ρ hdec
      rw [map_add] at hh
      rw [hρ0 (αY - (n : ℂ) • y₀) huY, hmap ρ n y₀] at hh
      exact hh
    have e3 : τ αX = τ (αX - (m : ℂ) • x₀) + (m : ℂ) • τ x₀ := by
      have hdec : αX = (αX - (m : ℂ) • x₀) + (m : ℂ) • x₀ := by abel
      have hh := congrArg τ hdec
      rw [map_add] at hh
      rw [hmap τ m x₀] at hh
      exact hh
    have e4 : τ αY = τ (αY - (n : ℂ) • y₀) + (n : ℂ) • τ y₀ := by
      have hdec : αY = (αY - (n : ℂ) • y₀) + (n : ℂ) • y₀ := by abel
      have hh := congrArg τ hdec
      rw [map_add] at hh
      rw [hmap τ n y₀] at hh
      exact hh
    -- the key identity comparing the images of `x₀` and `y₀`
    have hkey : (m : ℂ) • σ x₀ + (n : ℂ) • ρ y₀ = (m : ℂ) • τ x₀ + (n : ℂ) • τ y₀ := by
      by_cases hy1 : y₀ 1 = 0
      · have hx1 : x₀ 1 = 0 := by rw [hax, hy1, mul_zero]
        have hσx₀ : σ x₀ = τ x₀ :=
          hσ0 x₀ (by rw [mem_zSpan0]; exact ⟨self_mem_zSpan hx₀, hx1⟩)
        have hρy₀ : ρ y₀ = τ y₀ :=
          hρ0 y₀ (by rw [mem_zSpan0]; exact ⟨self_mem_zSpan hy₀, hy1⟩)
        rw [hσx₀, hρy₀]
      · have hmna : m * (a : ℤ) + n = 0 := by
          rcases mul_eq_zero.mp hmany with h | h
          · exact_mod_cast h
          · exact absurd h hy1
        have hrel' : σ x₀ - (a : ℂ) • ρ y₀ = τ x₀ - (a : ℂ) • τ y₀ := by
          have h1 : τ (x₀ - (a : ℂ) • y₀) = τ x₀ - (a : ℂ) • τ y₀ := by
            rw [map_sub, hmapNat τ a y₀]
          rw [← h1]; exact hrel.symm
        have hsub : σ x₀ - τ x₀ = (a : ℂ) • (ρ y₀ - τ y₀) := by
          rw [smul_sub]
          have h0 : σ x₀ - (a : ℂ) • ρ y₀ - (τ x₀ - (a : ℂ) • τ y₀) = 0 := by
            rw [hrel', sub_self]
          have h1 : σ x₀ - τ x₀ - ((a : ℂ) • ρ y₀ - (a : ℂ) • τ y₀) = 0 := by
            rw [← h0]; abel
          exact sub_eq_zero.mp h1
        have h4 : (m : ℂ) • (σ x₀ - τ x₀) + (n : ℂ) • (ρ y₀ - τ y₀) = 0 := by
          rw [hsub, smul_smul, ← add_smul]
          have hc : (m : ℂ) * (a : ℂ) + (n : ℂ) = ((m * (a : ℤ) + n : ℤ) : ℂ) := by
            push_cast; ring
          rw [hc, hmna, Int.cast_zero, zero_smul]
        have h5 : (m : ℂ) • σ x₀ + (n : ℂ) • ρ y₀
            - ((m : ℂ) • τ x₀ + (n : ℂ) • τ y₀) = 0 := by
          rw [smul_sub, smul_sub] at h4
          rw [← h4]; abel
        exact sub_eq_zero.mp h5
    have hmain : σ αX + ρ αY = τ αX + τ αY := by
      calc σ αX + ρ αY
          = (τ (αX - (m : ℂ) • x₀) + τ (αY - (n : ℂ) • y₀))
              + ((m : ℂ) • σ x₀ + (n : ℂ) • ρ y₀) := by rw [e1, e2]; abel
        _ = (τ (αX - (m : ℂ) • x₀) + τ (αY - (n : ℂ) • y₀))
              + ((m : ℂ) • τ x₀ + (n : ℂ) • τ y₀) := by rw [hkey]
        _ = τ αX + τ αY := by rw [e3, e4]; abel
    have hLHS : (∑ z : ↥(X ∪ Y), (c z : ℂ) • φ (z : H → ℂ)) = σ αX + ρ αY := by
      rw [Finset.sum_congr rfl (fun z _ => by rw [hcA_apply z])]
      rw [sum_subtype_union hXY (fun v : H → ℂ => (cA v : ℂ) • φ v)]
      congr 1
      · have h1 : (∑ x : ↥X, (cA (x : H → ℂ) : ℂ) • φ (x : H → ℂ))
            = ∑ x : ↥X, (cX x : ℂ) • σ (x : H → ℂ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hφX (x : H → ℂ) x.2]
        have hσeq : σ αX = ∑ x : ↥X, (cX x : ℂ) • σ (x : H → ℂ) := by
          show σ (∑ x : ↥X, (cX x : ℂ) • (x : H → ℂ)) = _
          rw [map_sum]
          exact Finset.sum_congr rfl fun x _ => hmap σ (cX x) (x : H → ℂ)
        rw [h1, ← hσeq]
      · have h2 : (∑ y : ↥Y, (cA (y : H → ℂ) : ℂ) • φ (y : H → ℂ))
            = ∑ y : ↥Y, (cY y : ℂ) • ρ (y : H → ℂ) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hφY (y : H → ℂ) y.2]
        have hρeq : ρ αY = ∑ y : ↥Y, (cY y : ℂ) • ρ (y : H → ℂ) := by
          show ρ (∑ y : ↥Y, (cY y : ℂ) • (y : H → ℂ)) = _
          rw [map_sum]
          exact Finset.sum_congr rfl fun y _ => hmap ρ (cY y) (y : H → ℂ)
        rw [h2, ← hρeq]
    rw [hLHS, hαeq, map_add, hmain]
  -- assemble
  obtain ⟨T, hTagree, hTiso, hTval⟩ :=
    extend_of_gram (S := X ∪ Y) (τ := τ) (φ := φ) hgram hcompat
  exact ⟨T, hTagree, hTiso, fun z hz => by
    rw [hTval z hz]
    rcases Finset.mem_union.mp hz with hzX | hzY
    · rw [hφX z hzX]; exact hσV z hzX
    · rw [hφY z hzY]; exact hρV z hzY⟩

end Work.FeitSibley.Coherence
