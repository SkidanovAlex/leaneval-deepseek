import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.CharCore.Main
import Submission.Work.NormalComplement.AppVII.CenterFinrankLe

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

noncomputable section

open Classical

open scoped BigOperators MonoidAlgebra

variable {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]

/-! ## The proof

The `toK χ` (`χ ∈ Irr A`) are non-zero pairwise orthogonal central idempotents of `k[A]`, and
`Work.CharCore.card_irr` together with `Work.NormalComplement.AppVII.CenterFinrankLe` (the
coefficient map on conjugacy-class representatives injects `Z(k[A])` into `ConjClasses A → k`)
gives `dim_k Z(k[A]) = (Irr A).card`.  Since non-zero pairwise orthogonal idempotents of the
centre are linearly independent, the `toK χ` form a `k`-basis of `Z(k[A])`.

Given a central idempotent `f` with `f * toK χ = f`, write `f = ∑_ψ c ψ • toK ψ` in that basis.
Multiplying by `toK χ` and using orthogonality of the `toK ψ` leaves `f = c χ • toK χ`;
idempotence of `f` then gives `c χ ^ 2 = c χ`, so `c χ ∈ {0, 1}` and `f = 0` or `f = toK χ`.
-/

/-- Non-zero pairwise orthogonal idempotents of the centre of a `k`-algebra are linearly
independent over `k`. -/
theorem linearIndependent_center_of_orthogonal_idempotents {k : Type*} [Field k] {R : Type*}
    [Ring R] [Algebra k R] {ι : Type*} [Fintype ι]
    (f : ι → ↥(Subalgebra.center k R)) (hidem : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (hne : ∀ i, f i ≠ 0) :
    LinearIndependent k f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun x : ↥(Subalgebra.center k R) => x * f i) hg
  rw [Finset.sum_mul, zero_mul] at h
  have hterm : ∀ j : ι, (g j • f j) * f i = if j = i then g i • f i else 0 := by
    intro j
    by_cases hj : j = i
    · rw [hj, smul_mul_assoc, hidem]
      simp
    · rw [smul_mul_assoc, horth j i hj, smul_zero]
      simp [hj]
  rw [show (∑ j, (g j • f j) * f i) = g i • f i from by
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]] at h
  by_contra hg0
  have h2 : f i = 0 := by
    have h3 : (g i)⁻¹ • (g i • f i) = (g i)⁻¹ • (0 : ↥(Subalgebra.center k R)) := by rw [h]
    rwa [smul_smul, inv_mul_cancel₀ hg0, one_smul, smul_zero] at h3
  exact hne i h2

/-- **The reduced idempotents `toK χ` are primitive central idempotents.**

Let `k = F̄_r`, `A` finite, `r ∤ |A|`, and suppose the elements `toK hcop χ hχ ∈ k[A]`
(χ ∈ Irr A) are central idempotents, non-zero, pairwise orthogonal, and sum to `1`.
Then each of them is a **primitive** central idempotent, i.e. for every central idempotent `f`
with `f * toK hcop χ hχ = f` one has `f = 0 ∨ f = toK hcop χ hχ`.

Route: `k[A]` is semisimple (Maschke; `r ∤ |A|` gives `NeZero (Nat.card A : k)`), and
`k = F̄_r` is a splitting field.

1. `dim_k Z(k[A]) = Nat.card (ConjClasses A)`: the class sums
   `Σ_{x ∈ class g} single x 1` form a basis of the centre.  They are central; they span,
   because `x` commuting with every `single g 1` forces `x` to be constant on conjugacy
   classes; and they are linearly independent since their supports are disjoint.
2. `#(central primitive idempotents) ≤ dim_k Z(k[A])`: distinct primitive central idempotents
   are orthogonal, hence linearly independent.
3. `|Irr A| ≤ #(central primitive idempotents)`: every non-zero central idempotent `e` is a sum
   of `≥ 1` primitive central idempotents (if `e` is not primitive, `e = f + (e - f)` with
   `f, e - f` non-zero orthogonal central idempotents, and one descends on, say,
   `Module.finrank k (Ideal.span {e})`).
4. `Work.CharCore.card_irr : (Irr A).card = Nat.card (ConjClasses A)`, so the three quantities
   are all equal, in particular `#(central primitive idempotents) = |Irr A|`.
5. The family `(toK hcop χ hχ)_{χ ∈ Irr A}` consists of `|Irr A|` non-zero orthogonal central
   idempotents summing to `1`; decompose each into its set of primitive summands: these are
   non-empty pairwise disjoint subsets of the set of all primitive central idempotents, whose
   cardinality equals the number of parts, so each part is a singleton.

Alternative route via Wedderburn–Artin
(`IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing` / `..._finite`):
`k[A] ≅ ∏ᵢ M_{nᵢ}(k)`, whose central primitive idempotents are the coordinate identities
`δᵢ`; the number of factors is `dim_k Z(k[A]) = #(ConjClasses A)`. -/
theorem ToKPrimitive {A : Type*} [Group A] [Fintype A] {r : ℕ} [Fact r.Prime]
    (hcop : Nat.Coprime r (Nat.card A))
    (hprops :
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
          Work.Hering.AppVII.IsCentralIdempotent (Work.Hering.AppVII.toK hcop χ hχ)) ∧
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A), Work.Hering.AppVII.toK hcop χ hχ ≠ 0) ∧
      (∀ (χ χ' : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A), χ ≠ χ' →
          Work.Hering.AppVII.toK hcop χ hχ * Work.Hering.AppVII.toK hcop χ' hχ' = 0) ∧
      (Finset.sum (Work.CharCore.Irr A).attach (fun x => Work.Hering.AppVII.toK hcop x.1 x.2) = 1) ∧
      (∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A) (z : A), χ z = χ 1 →
          Work.Hering.AppVII.toK hcop χ hχ *
            MonoidAlgebra.single z (1 : Work.Hering.AppVII.BrauerField r) =
          Work.Hering.AppVII.toK hcop χ hχ)) :
    ∀ (χ : A → ℂ) (hχ : χ ∈ Work.CharCore.Irr A),
      Work.Hering.AppVII.IsPrimitiveCentralIdempotent (Work.Hering.AppVII.toK hcop χ hχ) := by
  classical
  intro χ hχ
  obtain ⟨hcen, hne0, horth, _hsum, _hsingle⟩ := hprops
  refine ⟨hcen χ hχ, hne0 χ hχ, ?_⟩
  intro f hf hfe
  -- the reduced idempotents, as elements of the centre of `k[A]`
  have hfac : ∀ (ψ : A → ℂ) (hψ : ψ ∈ Work.CharCore.Irr A),
      Work.Hering.AppVII.toK hcop ψ hψ ∈ Subalgebra.center (Work.Hering.AppVII.BrauerField r)
        (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A) :=
    fun ψ hψ => Subalgebra.mem_center_iff.mpr (hcen ψ hψ).2
  let e : ↥(Work.CharCore.Irr A) → ↥(Subalgebra.center (Work.Hering.AppVII.BrauerField r)
      (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) :=
    fun ψ => ⟨Work.Hering.AppVII.toK hcop ψ.1 ψ.2, hfac ψ.1 ψ.2⟩
  have hLI : LinearIndependent (Work.Hering.AppVII.BrauerField r) e := by
    refine linearIndependent_center_of_orthogonal_idempotents e ?_ ?_ ?_
    · intro i
      apply Subtype.ext
      exact (hcen i.1 i.2).1
    · intro i j hij
      apply Subtype.ext
      exact horth i.1 j.1 i.2 j.2 (fun h => hij (Subtype.ext h))
    · intro i h
      exact hne0 i.1 i.2 (Subtype.ext_iff.mp h)
  -- `|Irr A| = dim_k Z(k[A])`
  have hle1 : Fintype.card ↥(Work.CharCore.Irr A) ≤
      Module.finrank (Work.Hering.AppVII.BrauerField r)
        ↥(Subalgebra.center (Work.Hering.AppVII.BrauerField r)
          (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) :=
    hLI.fintype_card_le_finrank
  have hle2 : Module.finrank (Work.Hering.AppVII.BrauerField r)
      ↥(Subalgebra.center (Work.Hering.AppVII.BrauerField r)
        (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) ≤ (Work.CharCore.Irr A).card := by
    rw [Work.CharCore.card_irr]
    exact CenterFinrankLe
  have hcard : Fintype.card ↥(Work.CharCore.Irr A) =
      Module.finrank (Work.Hering.AppVII.BrauerField r)
        ↥(Subalgebra.center (Work.Hering.AppVII.BrauerField r)
          (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) :=
    le_antisymm hle1 (by rw [Fintype.card_coe]; exact hle2)
  have htop : Submodule.span (Work.Hering.AppVII.BrauerField r) (Set.range e) = ⊤ :=
    hLI.span_eq_top_of_card_eq_finrank' hcard
  -- expand `f` in the basis
  have hfc : f ∈ Subalgebra.center (Work.Hering.AppVII.BrauerField r)
      (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A) :=
    Subalgebra.mem_center_iff.mpr hf.2
  let fZ : ↥(Subalgebra.center (Work.Hering.AppVII.BrauerField r)
      (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) := ⟨f, hfc⟩
  have hmem : fZ ∈ Submodule.span (Work.Hering.AppVII.BrauerField r) (Set.range e) := by
    rw [htop]
    trivial
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (Work.Hering.AppVII.BrauerField r)).mp hmem
  have hcR : (∑ i : ↥(Work.CharCore.Irr A),
      c i • Work.Hering.AppVII.toK hcop i.1 i.2) = f := by
    have h := congrArg (fun z : ↥(Subalgebra.center (Work.Hering.AppVII.BrauerField r)
        (MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) =>
      (z : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A)) hc
    simpa [e, fZ] using h
  -- multiply by `toK χ` and use orthogonality
  have key : f * Work.Hering.AppVII.toK hcop χ hχ =
      c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) • Work.Hering.AppVII.toK hcop χ hχ := by
    rw [← hcR, Finset.sum_mul]
    have hsum2 : (∑ i : ↥(Work.CharCore.Irr A),
        (c i • Work.Hering.AppVII.toK hcop i.1 i.2) * Work.Hering.AppVII.toK hcop χ hχ) =
        (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) •
          Work.Hering.AppVII.toK hcop χ hχ) * Work.Hering.AppVII.toK hcop χ hχ := by
      refine Finset.sum_eq_single (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) ?_ ?_
      · intro b _ hb
        rw [smul_mul_assoc, horth b.1 χ b.2 hχ (fun h => hb (Subtype.ext h)), smul_zero]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    rw [hsum2, smul_mul_assoc, (hcen χ hχ).1]
  have hfeq : f = c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) •
      Work.Hering.AppVII.toK hcop χ hχ :=
    (key ▸ hfe).symm
  -- idempotence forces the coefficient into `{0, 1}`
  have hff : (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) • Work.Hering.AppVII.toK hcop χ hχ) *
      (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) • Work.Hering.AppVII.toK hcop χ hχ) =
      c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) • Work.Hering.AppVII.toK hcop χ hχ := by
    have h := hf.1
    rw [hfeq] at h
    exact h
  have hcc : (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩ - c ⟨χ, hχ⟩) •
      Work.Hering.AppVII.toK hcop χ hχ = 0 := by
    have h1 : (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) • Work.Hering.AppVII.toK hcop χ hχ) *
        (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) • Work.Hering.AppVII.toK hcop χ hχ) =
        (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩) •
          Work.Hering.AppVII.toK hcop χ hχ := by
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, (hcen χ hχ).1]
    rw [sub_smul, ← h1, hff, sub_self]
  have hczero : c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩ - c ⟨χ, hχ⟩ = 0 := by
    by_contra hne
    have he0 : Work.Hering.AppVII.toK hcop χ hχ = 0 := by
      have h3 : (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩ - c ⟨χ, hχ⟩)⁻¹ •
          ((c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩ - c ⟨χ, hχ⟩) •
            Work.Hering.AppVII.toK hcop χ hχ) =
          (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩ - c ⟨χ, hχ⟩)⁻¹ •
            (0 : MonoidAlgebra (Work.Hering.AppVII.BrauerField r) A) := by
        rw [hcc]
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] at h3
      exact h3
    exact hne0 χ hχ he0
  rcases eq_or_ne (c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A))) 0 with hzero | hnonzero
  · left
    rw [hfeq, hzero, zero_smul]
  · right
    have hc1 : c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * c ⟨χ, hχ⟩ = c ⟨χ, hχ⟩ :=
      sub_eq_zero.mp hczero
    have hmul : c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) * (c ⟨χ, hχ⟩ - 1) = 0 := by
      rw [mul_sub, mul_one, hc1, sub_self]
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact absurd h1 hnonzero
    · have hone : c (⟨χ, hχ⟩ : ↥(Work.CharCore.Irr A)) = 1 := sub_eq_zero.mp h1
      rw [hfeq, hone, one_smul]

end

end Work.NormalComplement.AppVII
