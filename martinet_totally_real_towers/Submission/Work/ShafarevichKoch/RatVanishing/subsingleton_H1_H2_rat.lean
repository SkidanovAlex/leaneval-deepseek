/-
Copyright: the martinet_totally_real_towers team.

# Vanishing of `H¹` and `H²` of a compact totally disconnected group with `ℚ`-coefficients

**Module** `Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat`.

Let `G` be a group with a topology making it a topological group, compact and totally
disconnected, and let `ℚ` be a discrete `G`-module on which `G` acts trivially.  Then the
continuous cohomology groups `H¹(G, ℚ)` and `H²(G, ℚ)` of the chapter
`Submission.Work.ConCohomology` are trivial (subsingletons).

The mathematical content is that `ℚ` is *uniquely divisible*, while `G` is compact:
* `H¹`: a `1`-cocycle is a locally constant additive character `φ : G → ℚ`; its kernel is an
  open subgroup, hence of finite index in the compact group `G`, and a finite group `G/K`
  admits no nontrivial additive character into the torsion-free group `ℚ`.
* `H²`: a locally constant `2`-cocycle is invariant under right translation by an open normal
  subgroup `N ⊆ G` (this uses only the cocycle identity and compactness), hence descends to a
  `2`-cocycle on the finite group `G/N`, where it is a coboundary because `ℚ` is a `ℚ`-vector
  space (average over the finite group and divide by its order).

The auxiliary lemmas proved here are:
* `exists_open_nhds_one_right`, `exists_open_nhds_one_left` — the compactness/local-constancy
  lemmas producing one-sided translation invariance;
* `exists_coboundary_of_finite_twoCocycle_rat` — the averaging lemma for a finite group with
  coefficients in `ℚ`.
-/

import Mathlib
import Submission.Work.ConCohomology.All

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ShafarevichKoch.RatVanishing

open Work.ConCohomology

/-! ### Translation invariance of a locally constant function on a compact group -/

/-- **Right translation invariance in the second variable.**  If `f : G × G → M` is locally
constant and `f (-, 1)` is constant, then there is an open neighbourhood `B` of `1` such that
`f (x, y * n) = f (x, y)` … more precisely `f (x, b) = f (x, 1)` for all `x : G` and `b ∈ B`.

The proof uses that `f` is locally constant at each point `(x, 1)`, and compactness of `G` to
pass to finitely many `x`; `f (x, 1)` being independent of `x` then gives the claim. -/
lemma exists_open_nhds_one_right {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type*} {f : G × G → M} (hf : IsLocallyConstant f) (h1 : ∀ x : G, f (x, 1) = f (1, 1)) :
    ∃ B : Set G, IsOpen B ∧ (1 : G) ∈ B ∧ ∀ x y : G, y ∈ B → f (x, y) = f (x, 1) := by
  classical
  have key : ∀ x : G, ∃ A B : Set G, IsOpen A ∧ x ∈ A ∧ IsOpen B ∧ (1 : G) ∈ B ∧
      ∀ a b : G, a ∈ A → b ∈ B → f (a, b) = f (x, 1) := by
    intro x
    obtain ⟨O, hO, hxO, hcO⟩ := hf.exists_open (x, 1)
    obtain ⟨A, B, hA, hB, hxA, h1B, hAB⟩ := isOpen_prod_iff.mp hO x 1 hxO
    exact ⟨A, B, hA, hxA, hB, h1B, fun a b ha hb => hcO (a, b) (hAB ⟨ha, hb⟩)⟩
  choose A B hAopen hxA hBopen h1B hconst using key
  have hcover : (Set.univ : Set G) ⊆ ⋃ x : G, A x := fun y _ => Set.mem_iUnion.mpr ⟨y, hxA y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover A hAopen hcover
  refine ⟨⋂ x ∈ t, B x, isOpen_biInter_finset (fun x _ => hBopen x), ?_, ?_⟩
  · rw [Set.mem_iInter]; intro x; rw [Set.mem_iInter]; exact fun _ => h1B x
  · intro p q hq
    have hq' : p ∈ ⋃ i ∈ t, A i := ht (Set.mem_univ p)
    simp only [Set.mem_iUnion] at hq'
    obtain ⟨x₀, hx₀t, hpx₀⟩ := hq'
    have hqB : q ∈ B x₀ := by
      have h := hq; simp only [Set.mem_iInter] at h; exact h x₀ hx₀t
    rw [hconst x₀ p q hpx₀ hqB, h1 x₀, ← h1 p]

/-- **Left translation invariance in the first variable.**  If `f : G × G → M` is locally
constant and `f (1, -)` is constant, then there is an open neighbourhood `A` of `1` with
`f (a, y) = f (1, y)` for all `y : G` and `a ∈ A`; equivalently `f` is invariant under left
translation of the first variable by elements of `A`. -/
lemma exists_open_nhds_one_left {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type*} {f : G × G → M} (hf : IsLocallyConstant f) (h2 : ∀ y : G, f (1, y) = f (1, 1)) :
    ∃ A : Set G, IsOpen A ∧ (1 : G) ∈ A ∧ ∀ x y : G, x ∈ A → f (x, y) = f (1, y) := by
  classical
  have key : ∀ y : G, ∃ A B : Set G, IsOpen A ∧ (1 : G) ∈ A ∧ IsOpen B ∧ y ∈ B ∧
      ∀ a b : G, a ∈ A → b ∈ B → f (a, b) = f (1, y) := by
    intro y
    obtain ⟨O, hO, hyO, hcO⟩ := hf.exists_open (1, y)
    obtain ⟨A, B, hA, hB, h1A, hyB, hAB⟩ := isOpen_prod_iff.mp hO 1 y hyO
    exact ⟨A, B, hA, h1A, hB, hyB, fun a b ha hb => hcO (a, b) (hAB ⟨ha, hb⟩)⟩
  choose A B hAopen h1A hBopen hyB hconst using key
  have hcover : (Set.univ : Set G) ⊆ ⋃ y : G, B y := fun y _ => Set.mem_iUnion.mpr ⟨y, hyB y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBopen hcover
  refine ⟨⋂ y ∈ t, A y, isOpen_biInter_finset (fun y _ => hAopen y), ?_, ?_⟩
  · rw [Set.mem_iInter]; intro y; rw [Set.mem_iInter]; exact fun _ => h1A y
  · intro p q hp
    have hp' : q ∈ ⋃ i ∈ t, B i := ht (Set.mem_univ q)
    simp only [Set.mem_iUnion] at hp'
    obtain ⟨y₀, hy₀t, hqy₀⟩ := hp'
    have hpA : p ∈ A y₀ := by
      have h := hp; simp only [Set.mem_iInter] at h; exact h y₀ hy₀t
    rw [hconst y₀ p q hpA hqy₀, h2 y₀, ← h2 q]

/-! ### The averaging lemma for a finite group with coefficients in `ℚ` -/

/-- **Averaging a `2`-cocycle over a finite group, with coefficients in `ℚ`.**  Let `c` be an
inhomogeneous `2`-cocycle (trivial action) on a finite group `Q`.  The averaged cochain
`σ ↦ |Q|⁻¹ * ∑_ρ c (σ, ρ)` is a `1`-cochain whose coboundary is `c`:
`x τ - x (σ * τ) + x σ = c σ τ`.  (This is the classical computation; the only point is that
`|Q|` is invertible in `ℚ`.) -/
lemma exists_coboundary_of_finite_twoCocycle_rat {Q : Type*} [Group Q] [Fintype Q]
    (c : Q → Q → ℚ) (hc : ∀ σ τ ρ : Q, c τ ρ - c (σ*τ) ρ + c σ (τ*ρ) - c σ τ = 0) :
    ∃ x : Q → ℚ, ∀ σ τ : Q, x τ - x (σ*τ) + x σ = c σ τ := by
  classical
  refine ⟨fun σ => ((Fintype.card Q : ℚ))⁻¹ * ∑ ρ : Q, c σ ρ, fun σ τ => ?_⟩
  have hN : ((Fintype.card Q : ℚ)) ≠ 0 := by
    haveI : Nonempty Q := ⟨1⟩
    exact_mod_cast Fintype.card_ne_zero
  have hstep : ∀ ρ : Q, c τ ρ - c (σ*τ) ρ + c σ ρ = c σ τ - c σ (τ*ρ) + c σ ρ := by
    intro ρ
    have h := hc σ τ ρ
    linarith
  have hreindex : (∑ ρ : Q, c σ (τ*ρ)) = ∑ ρ : Q, c σ ρ :=
    Equiv.sum_comp (Equiv.mulLeft τ) (fun ρ => c σ ρ)
  have hsum : (∑ ρ : Q, c τ ρ) - (∑ ρ : Q, c (σ*τ) ρ) + (∑ ρ : Q, c σ ρ)
      = ((Fintype.card Q : ℚ)) * c σ τ := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun ρ _ => hstep ρ), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hreindex]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [← mul_sub, ← mul_add, hsum, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-! ### Vanishing of `H¹` and `H²` -/

/-- **`H¹(G, ℚ)` is trivial for a compact totally disconnected `G` acting trivially on `ℚ`.**

A `1`-cocycle for the trivial action is a locally constant additive homomorphism `φ : G → ℚ`.
Its kernel is an open subgroup, hence of finite index; if `σ ^ n ∈ ker φ` with `n > 0` then
`n • φ σ = 0`, and `ℚ` is torsion-free, so `φ σ = 0`. -/
theorem subsingleton_H1_rat {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [DistribMulAction G ℚ] [IsDiscreteGModule G ℚ]
    (htriv : ∀ (σ : G) (q : ℚ), σ • q = q) :
    Subsingleton (H1 G ℚ) := by
  have hzero : ∀ φ : ContAddHom G ℚ, ∀ σ : G, φ σ = 0 := by
    intro φ σ
    have h1 : φ 1 = 0 := by
      have h := φ.map_mul 1 1
      rw [mul_one] at h
      have h2 : (0:ℚ) = φ 1 := add_left_cancel (by rw [add_zero]; exact h)
      exact h2.symm
    let K : Subgroup G :=
      { carrier := {x : G | φ x = 0}
        mul_mem' := by
          intro a b ha hb
          have ha' : φ a = 0 := ha
          have hb' : φ b = 0 := hb
          show φ (a * b) = 0
          rw [φ.map_mul, ha', hb', add_zero]
        one_mem' := h1
        inv_mem' := by
          intro a ha
          have ha' : φ a = 0 := ha
          have h := φ.map_mul a a⁻¹
          rw [mul_inv_cancel, h1, ha', zero_add] at h
          show φ a⁻¹ = 0
          exact h.symm }
    have hKopen : IsOpen (K : Set G) := (ContAddHom.isLocallyConstant φ).isOpen_fiber 0
    haveI : Finite (G ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKopen
    obtain ⟨n, hnpos, -, hnmem⟩ :=
      Subgroup.exists_pow_mem_of_index_ne_zero (H := K)
        (Subgroup.index_ne_zero_of_finite (H := K)) σ
    have hpow : ∀ m : ℕ, φ (σ^m) = m • φ σ := by
      intro m
      induction m with
      | zero => rw [pow_zero]; simp [h1]
      | succ k ih => rw [pow_succ, φ.map_mul, ih, succ_nsmul]
    have hz : φ (σ^n) = 0 := hnmem
    have hzero' : n • φ σ = 0 := by rw [← hpow n, hz]
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hnn : (n : ℚ) * φ σ = 0 := by simpa [nsmul_eq_mul] using hzero'
    exact (mul_eq_zero.mp hnn).resolve_left hn0
  haveI : Subsingleton (ContAddHom G ℚ) :=
    ⟨fun φ ψ => ContAddHom.ext fun σ => by rw [hzero φ σ, hzero ψ σ]⟩
  exact ⟨fun a b => (H1EquivContAddHom htriv).injective (Subsingleton.elim _ _)⟩

/-- **`H²(G, ℚ)` is trivial for a compact totally disconnected `G` acting trivially on `ℚ`.**

A locally constant `2`-cocycle is right-invariant under an open normal subgroup `N` (the
compactness lemmas above), so it descends to a `2`-cocycle on the finite group `G ⧸ N`, where
it is a coboundary by the averaging lemma `exists_coboundary_of_finite_twoCocycle_rat`.  Pulling
the resulting `1`-cochain back along `G → G ⧸ N` gives a locally constant cochain whose
coboundary is the original cocycle. -/
theorem subsingleton_H2_rat {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [DistribMulAction G ℚ] [IsDiscreteGModule G ℚ]
    (htriv : ∀ (σ : G) (q : ℚ), σ • q = q) :
    Subsingleton (H2 G ℚ) := by
  rw [QuotientAddGroup.subsingleton_iff]
  apply le_antisymm le_top
  intro z _
  rw [mem_B2', mem_B2]
  have hflc : IsLocallyConstant (z.1 : G×G → ℚ) :=
    (z.1 : LocallyConstant (G×G) ℚ).isLocallyConstant
  have hcocyc : ∀ σ τ ρ : G, (z.1 : G×G → ℚ) (τ,ρ) - (z.1 : G×G → ℚ) (σ*τ,ρ)
      + (z.1 : G×G → ℚ) (σ,τ*ρ) - (z.1 : G×G → ℚ) (σ,τ) = 0 := by
    intro σ τ ρ
    have h := mem_Z2.mp z.2 σ τ ρ
    rwa [htriv σ ((z.1 : G×G → ℚ) (τ,ρ))] at h
  have hcol1 : ∀ x : G, (z.1 : G×G → ℚ) (x, 1) = (z.1 : G×G → ℚ) (1,1) := by
    intro x
    have h := hcocyc x 1 1
    simp only [mul_one] at h
    linarith
  have hrow1 : ∀ y : G, (z.1 : G×G → ℚ) (1, y) = (z.1 : G×G → ℚ) (1,1) := by
    intro y
    have h := hcocyc 1 1 y
    simp only [one_mul] at h
    linarith
  obtain ⟨B, hBopen, h1B, hB⟩ :=
    exists_open_nhds_one_right (f := (z.1 : G×G → ℚ)) hflc hcol1
  obtain ⟨A, hAopen, h1A, hA⟩ :=
    exists_open_nhds_one_left (f := (z.1 : G×G → ℚ)) hflc hrow1
  have hABopen : IsOpen (A ∩ B) := hAopen.inter hBopen
  obtain ⟨N, hNsub⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hABopen ⟨h1A, h1B⟩
  let Ns : Subgroup G := N.toSubgroup
  haveI : Ns.Normal := N.isNormal'
  have hNsopen : IsOpen (Ns : Set G) := N.toOpenSubgroup.isOpen
  haveI : Finite (G ⧸ Ns) := Subgroup.quotient_finite_of_isOpen Ns hNsopen
  haveI : Fintype (G ⧸ Ns) := Fintype.ofFinite _
  have hNA : ∀ n : G, n ∈ Ns → n ∈ A := fun n hn => (hNsub hn).1
  have hNB : ∀ n : G, n ∈ Ns → n ∈ B := fun n hn => (hNsub hn).2
  have hinv2 : ∀ n : G, n ∈ Ns → ∀ σ τ : G,
      (z.1 : G×G → ℚ) (σ, τ*n) = (z.1 : G×G → ℚ) (σ, τ) := by
    intro n hn σ τ
    have h := hcocyc σ τ n
    rw [hB τ n (hNB n hn), hB (σ*τ) n (hNB n hn), hcol1 τ, hcol1 (σ*τ)] at h
    linarith
  have hinv1 : ∀ n : G, n ∈ Ns → ∀ σ τ : G,
      (z.1 : G×G → ℚ) (n*σ, τ) = (z.1 : G×G → ℚ) (σ, τ) := by
    intro n hn σ τ
    have h := hcocyc n σ τ
    rw [hA n (σ*τ) (hNA n hn), hA n σ (hNA n hn), hrow1 (σ*τ), hrow1 σ] at h
    linarith
  have hinv3 : ∀ n : G, n ∈ Ns → ∀ σ τ : G,
      (z.1 : G×G → ℚ) (σ*n, τ) = (z.1 : G×G → ℚ) (σ, τ) := by
    intro n hn σ τ
    have hconj : σ * n * σ⁻¹ ∈ Ns := (inferInstance : Ns.Normal).conj_mem n hn σ
    have hg : (σ*n*σ⁻¹)*σ = σ*n := by group
    calc (z.1 : G×G → ℚ) (σ*n, τ) = (z.1 : G×G → ℚ) ((σ*n*σ⁻¹)*σ, τ) := by rw [hg]
      _ = (z.1 : G×G → ℚ) (σ, τ) := hinv1 (σ*n*σ⁻¹) hconj σ τ
  let c : (G ⧸ Ns) → (G ⧸ Ns) → ℚ := fun q q' => (z.1 : G×G → ℚ) (q.out, q'.out)
  have hc : ∀ q q' q'' : G ⧸ Ns, c q' q'' - c (q*q') q'' + c q (q'*q'') - c q q' = 0 := by
    intro q q' q''
    show (z.1 : G×G → ℚ) (q'.out, q''.out) - (z.1 : G×G → ℚ) ((q*q').out, q''.out)
      + (z.1 : G×G → ℚ) (q.out, (q'*q'').out) - (z.1 : G×G → ℚ) (q.out, q'.out) = 0
    have hA1 : QuotientGroup.mk' Ns (q.out * q'.out) = QuotientGroup.mk' Ns (q*q').out := by
      have h1 : (↑(Quotient.out q) : G ⧸ Ns) = q := QuotientGroup.out_eq' q
      have h2 : (↑(Quotient.out q') : G ⧸ Ns) = q' := QuotientGroup.out_eq' q'
      have h3 : (↑(Quotient.out (q*q')) : G ⧸ Ns) = q*q' := QuotientGroup.out_eq' (q*q')
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
      rw [h1, h2, h3]
    obtain ⟨w, hwN, hw⟩ := (QuotientGroup.mk'_eq_mk' Ns).mp hA1
    have hA2 : QuotientGroup.mk' Ns (q'.out * q''.out) = QuotientGroup.mk' Ns (q'*q'').out := by
      have h1 : (↑(Quotient.out q') : G ⧸ Ns) = q' := QuotientGroup.out_eq' q'
      have h2 : (↑(Quotient.out q'') : G ⧸ Ns) = q'' := QuotientGroup.out_eq' q''
      have h3 : (↑(Quotient.out (q'*q'')) : G ⧸ Ns) = q'*q'' := QuotientGroup.out_eq' (q'*q'')
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
      rw [h1, h2, h3]
    obtain ⟨w', hw'N, hw'⟩ := (QuotientGroup.mk'_eq_mk' Ns).mp hA2
    have step1 : (z.1 : G×G → ℚ) ((q*q').out, q''.out)
        = (z.1 : G×G → ℚ) (q.out * q'.out, q''.out) := by
      rw [← hw]
      exact hinv3 w hwN (q.out * q'.out) q''.out
    have step2 : (z.1 : G×G → ℚ) (q.out, (q'*q'').out)
        = (z.1 : G×G → ℚ) (q.out, q'.out * q''.out) := by
      rw [← hw']
      exact hinv2 w' hw'N q.out (q'.out * q''.out)
    rw [step1, step2]
    exact hcocyc q.out q'.out q''.out
  obtain ⟨x, hx⟩ := exists_coboundary_of_finite_twoCocycle_rat c hc
  have hmk : IsLocallyConstant (fun σ : G => QuotientGroup.mk' Ns σ) :=
    isLocallyConstant_of_le_open_ker (QuotientGroup.mk' Ns) Ns hNsopen (by rw [QuotientGroup.ker_mk'])
  have key : ∀ σ τ : G, x (QuotientGroup.mk' Ns τ) - x (QuotientGroup.mk' Ns (σ*τ))
      + x (QuotientGroup.mk' Ns σ) = (z.1 : G×G → ℚ) (σ, τ) := by
    intro σ τ
    rw [show QuotientGroup.mk' Ns (σ*τ) = QuotientGroup.mk' Ns σ * QuotientGroup.mk' Ns τ
      from map_mul _ _ _, hx (QuotientGroup.mk' Ns σ) (QuotientGroup.mk' Ns τ)]
    show (z.1 : G×G → ℚ) ((QuotientGroup.mk' Ns σ).out, (QuotientGroup.mk' Ns τ).out)
      = (z.1 : G×G → ℚ) (σ, τ)
    obtain ⟨w₁, hw₁N, hw₁⟩ : ∃ v ∈ Ns, σ * v = (QuotientGroup.mk' Ns σ).out :=
      (QuotientGroup.mk'_eq_mk' Ns).mp (by
        have h1 : (↑(Quotient.out (QuotientGroup.mk' Ns σ)) : G ⧸ Ns) = QuotientGroup.mk' Ns σ :=
          QuotientGroup.out_eq' _
        simp only [QuotientGroup.mk'_apply]
        exact h1.symm)
    obtain ⟨w₂, hw₂N, hw₂⟩ : ∃ v ∈ Ns, τ * v = (QuotientGroup.mk' Ns τ).out :=
      (QuotientGroup.mk'_eq_mk' Ns).mp (by
        have h1 : (↑(Quotient.out (QuotientGroup.mk' Ns τ)) : G ⧸ Ns) = QuotientGroup.mk' Ns τ :=
          QuotientGroup.out_eq' _
        simp only [QuotientGroup.mk'_apply]
        exact h1.symm)
    rw [← hw₂, hinv2 w₂ hw₂N (QuotientGroup.mk' Ns σ).out τ, ← hw₁, hinv3 w₁ hw₁N σ τ]
  refine ⟨⟨fun σ : G => x (QuotientGroup.mk' Ns σ), hmk.comp x⟩, ?_⟩
  ext p
  obtain ⟨σ, τ⟩ := p
  simp only [d1Hom_apply, htriv]
  show x (QuotientGroup.mk' Ns τ) - x (QuotientGroup.mk' Ns (σ * τ)) + x (QuotientGroup.mk' Ns σ)
    = (z.1 : G×G → ℚ) (σ, τ)
  exact key σ τ

/-- **The requested lemma.**  For a compact totally disconnected topological group `G` with a
discrete trivial action on `ℚ`, both `H¹(G, ℚ)` and `H²(G, ℚ)` are subsingletons. -/
theorem subsingleton_H1_H2_rat {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    [DistribMulAction G ℚ] [Work.ConCohomology.IsDiscreteGModule G ℚ]
    (htriv : ∀ (σ : G) (q : ℚ), σ • q = q) :
    Subsingleton (Work.ConCohomology.H1 G ℚ) ∧ Subsingleton (Work.ConCohomology.H2 G ℚ) :=
  ⟨subsingleton_H1_rat htriv, subsingleton_H2_rat htriv⟩

end Work.ShafarevichKoch.RatVanishing
