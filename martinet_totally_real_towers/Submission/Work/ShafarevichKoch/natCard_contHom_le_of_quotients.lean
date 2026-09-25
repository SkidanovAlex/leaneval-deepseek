import Mathlib

/-!
# `Work.ShafarevichKoch.natCard_contHom_le_of_quotients`

**The number of continuous characters `G → ℤ/2` of a compact totally disconnected group is
bounded by `2 ^ s` as soon as every *finite quotient* `G ⧸ U` (by an open normal subgroup `U`)
has at most `2 ^ s` characters.**

This is the group-theoretic counting lemma behind the Shafarevich--Koch relation count: it
upgrades a uniform bound on the `𝔽₂`-duals of the finite quotients of `G` to the same bound on
the dual of `G` itself.

The proof is the elementary "every character factors through a finite quotient" argument:

* a continuous homomorphism `χ : G →* Multiplicative (ZMod 2)` has an *open* kernel `ker χ`
  (the target is discrete), and `ker χ ∈ S`, where
  `S := {K | ∃ χ, Continuous χ ∧ χ ≠ 1 ∧ ker χ = K}` is the set of kernels of nontrivial
  continuous characters;
* if `S` is **infinite**, then the map sending `K ∈ S` to a chosen character with kernel `K` is
  injective, so the type of continuous characters is infinite, and `Nat.card` of an infinite type
  is `0`, which is `≤ 2 ^ s`;
* if `S` is **finite**, then `U₀ := ⨅ K ∈ S, K` is an open normal subgroup (a finite intersection
  of open subgroups), and *every* continuous character is trivial on `U₀` — it is either trivial,
  or its kernel lies in `S` and hence contains `U₀`.  The map `χ ↦ (χ̄ : G ⧸ U₀ →* ℤ/2)` induced
  on the quotient is injective, and the target has at most `2 ^ s` elements by hypothesis.

The kernel of a homomorphism into a two-element group determines it (the target has exactly one
non-identity element), which is what makes the count of characters a count of kernels.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The kernels of the nontrivial continuous characters of `G` with values in
`Multiplicative (ZMod 2)`. -/
def kerSet (G : Type*) [Group G] [TopologicalSpace G] : Set (Subgroup G) :=
  {K | ∃ φ : G →* Multiplicative (ZMod 2), Continuous φ ∧ φ ≠ 1 ∧ φ.ker = K}

/-- The kernel of a continuous homomorphism into the discrete group `Multiplicative (ZMod 2)` is
open. -/
lemma isOpen_ker_of_continuous_zmodTwo (φ : G →* Multiplicative (ZMod 2)) (hφ : Continuous φ) :
    IsOpen ((φ.ker : Subgroup G) : Set G) := by
  have h : IsOpen (φ ⁻¹' ({1} : Set (Multiplicative (ZMod 2)))) :=
    hφ.isOpen_preimage _ (isOpen_discrete _)
  convert h using 1
  ext x
  simp [MonoidHom.mem_ker]

/-- An element of `kerSet G` is open. -/
lemma isOpen_of_mem_kerSet {K : Subgroup G} (hK : K ∈ kerSet G) : IsOpen ((K : Subgroup G) : Set G) := by
  obtain ⟨φ, hφc, -, hφK⟩ := hK
  rw [← hφK]
  exact isOpen_ker_of_continuous_zmodTwo φ hφc

/-- An element of `kerSet G` is a kernel, hence normal. -/
lemma normal_of_mem_kerSet {K : Subgroup G} (hK : K ∈ kerSet G) : K.Normal := by
  obtain ⟨φ, -, -, hφK⟩ := hK
  rw [← hφK]
  exact MonoidHom.normal_ker φ

/-- In a group of cardinality `2`, every element is either `1` or any prescribed nonidentity
element. -/
lemma eq_one_or_eq_of_natCard_eq_two {A : Type*} [Group A] (hA : Nat.card A = 2) {a : A} (ha : a ≠ 1) :
    ∀ b : A, b = 1 ∨ b = a := by
  obtain ⟨b, hbne, hb⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro y
  rcases eq_or_ne y 1 with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [hb y h, hb a ha])

/-- A nontrivial homomorphism into `Multiplicative (ZMod 2)` is surjective: an image that is not
the identity element generates the two-element group. -/
lemma surjective_zmodTwo_of_ne_one (φ : G →* Multiplicative (ZMod 2)) (hφ : φ ≠ 1) :
    Function.Surjective φ := by
  have hex : ∃ x : G, φ x ≠ 1 := by
    by_contra h
    exact hφ (MonoidHom.ext fun x => not_not.mp (not_exists.mp h x))
  obtain ⟨x₀, hx₀⟩ := hex
  intro y
  rcases eq_one_or_eq_of_natCard_eq_two (A := Multiplicative (ZMod 2)) (by simp) hx₀ y with h | h
  · exact ⟨1, by rw [h, map_one]⟩
  · exact ⟨x₀, h.symm⟩

/-- A homomorphism into a group of cardinality `2` is determined by its kernel. -/
lemma eq_of_ker_eq_zmodTwo (φ ψ : G →* Multiplicative (ZMod 2)) (h : φ.ker = ψ.ker) : φ = ψ := by
  ext x
  have key : φ x = 1 ↔ ψ x = 1 := by
    rw [← MonoidHom.mem_ker, h, MonoidHom.mem_ker]
  rcases eq_or_ne (φ x) 1 with h1 | h1
  · rw [h1, key.mp h1]
  · have h2 : ψ x ≠ 1 := fun hh => h1 (key.mpr hh)
    obtain ⟨b, hbne, hb⟩ := (Nat.card_eq_two_iff' (1 : Multiplicative (ZMod 2))).mp (by simp)
    rw [hb (φ x) h1, hb (ψ x) h2]

/-- If `kerSet G` is infinite, then so is the type of continuous characters of `G`: choose a
character with a prescribed kernel, which is injective because the kernel of a homomorphism into a
two-element group determines the homomorphism. -/
lemma infinite_contHom_of_infinite_kerSet (h : (kerSet G).Infinite) :
    Infinite {φ : G →* Multiplicative (ZMod 2) // Continuous φ} := by
  haveI : Infinite {K : Subgroup G // K ∈ kerSet G} := Set.infinite_coe_iff.mpr h
  let g : {K : Subgroup G // K ∈ kerSet G} → {φ : G →* Multiplicative (ZMod 2) // Continuous φ} :=
    fun K => ⟨K.2.choose, K.2.choose_spec.1⟩
  have hg : Function.Injective g := by
    intro K K' hKK'
    have h1 : (g K).1 = (g K').1 := congrArg Subtype.val hKK'
    have hK : K.1 = (g K).1.ker := K.2.choose_spec.2.2.symm
    have hK' : K'.1 = (g K').1.ker := K'.2.choose_spec.2.2.symm
    refine Subtype.ext ?_
    rw [hK, h1, ← hK']
  exact Infinite.of_injective g hg

theorem natCard_contHom_le_of_quotients {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (s : ℕ)
    (h : ∀ (U : Subgroup G) [U.Normal], IsOpen (U : Set G) →
      Nat.card {φ : G ⧸ U →* Multiplicative (ZMod 2) //
        Continuous (φ : G ⧸ U → Multiplicative (ZMod 2))} ≤ 2 ^ s) :
    Nat.card {φ : G →* Multiplicative (ZMod 2) //
      Continuous (φ : G → Multiplicative (ZMod 2))} ≤ 2 ^ s := by
  classical
  by_cases hS : (kerSet G).Finite
  · -- the finite case: all characters factor through the open normal subgroup `U₀ = ⨅ kerSet G`
    haveI : Finite {K : Subgroup G // K ∈ kerSet G} := hS.to_subtype
    have hKopen : ∀ K : {K : Subgroup G // K ∈ kerSet G}, IsOpen ((K.1 : Subgroup G) : Set G) :=
      fun K => isOpen_of_mem_kerSet K.2
    have hKnormal : ∀ K : {K : Subgroup G // K ∈ kerSet G}, K.1.Normal :=
      fun K => normal_of_mem_kerSet K.2
    let U₀ : Subgroup G := ⨅ K : {K : Subgroup G // K ∈ kerSet G}, K.1
    have hU₀eq : U₀ = ⨅ K : {K : Subgroup G // K ∈ kerSet G}, K.1 := rfl
    have hU₀open : IsOpen (U₀ : Set G) := by
      rw [hU₀eq, Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite hKopen
    haveI : U₀.Normal := Subgroup.normal_iInf_normal hKnormal
    -- every continuous character is trivial on `U₀`
    have hle : ∀ φ : {φ : G →* Multiplicative (ZMod 2) // Continuous φ}, U₀ ≤ φ.1.ker := by
      intro φ
      by_cases hφ : φ.1 = 1
      · have hker : φ.1.ker = ⊤ := by rw [hφ]; exact MonoidHom.ker_one
        rw [hker]
        exact le_top
      · have hmem : φ.1.ker ∈ kerSet G := ⟨φ.1, φ.2, hφ, rfl⟩
        exact iInf_le (fun K : {K : Subgroup G // K ∈ kerSet G} => K.1) ⟨φ.1.ker, hmem⟩
    haveI : DiscreteTopology (G ⧸ U₀) := QuotientGroup.discreteTopology hU₀open
    haveI : Finite (G ⧸ U₀) := Subgroup.quotient_finite_of_isOpen U₀ hU₀open
    haveI : Finite (G ⧸ U₀ →* Multiplicative (ZMod 2)) :=
      Finite.of_injective
        (fun f : G ⧸ U₀ →* Multiplicative (ZMod 2) => (f : G ⧸ U₀ → Multiplicative (ZMod 2)))
        (fun _ _ hf => MonoidHom.ext fun x => congrFun hf x)
    haveI : Finite {ψ : G ⧸ U₀ →* Multiplicative (ZMod 2) // Continuous ψ} :=
      Finite.of_injective Subtype.val (fun _ _ hψ => Subtype.ext hψ)
    let Ψ : {φ : G →* Multiplicative (ZMod 2) // Continuous φ} →
        {ψ : G ⧸ U₀ →* Multiplicative (ZMod 2) // Continuous ψ} :=
      fun φ => ⟨QuotientGroup.lift U₀ φ.1 (hle φ), continuous_of_discreteTopology⟩
    have hΨinj : Function.Injective Ψ := by
      intro φ ψ hφψ
      apply Subtype.ext
      refine MonoidHom.ext fun g => ?_
      have h1 : (QuotientGroup.lift U₀ φ.1 (hle φ)) (QuotientGroup.mk g)
          = (QuotientGroup.lift U₀ ψ.1 (hle ψ)) (QuotientGroup.mk g) := by
        have h2 := DFunLike.congr_fun (congrArg Subtype.val hφψ) (QuotientGroup.mk g)
        simpa only [Ψ] using h2
      simpa only [QuotientGroup.lift_mk'] using h1
    calc Nat.card {φ : G →* Multiplicative (ZMod 2) // Continuous φ}
        ≤ Nat.card {ψ : G ⧸ U₀ →* Multiplicative (ZMod 2) // Continuous ψ} :=
          Nat.card_le_card_of_injective Ψ hΨinj
      _ ≤ 2 ^ s := h U₀ hU₀open
  · -- the infinite case: infinitely many kernels give infinitely many characters
    haveI : Infinite {φ : G →* Multiplicative (ZMod 2) // Continuous φ} :=
      infinite_contHom_of_infinite_kerSet hS
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end Work.ShafarevichKoch
