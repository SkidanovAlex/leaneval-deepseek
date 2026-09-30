import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.exists_capH
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.EMFG.emHomologyFG
import Submission.Work.SSS.serreFGThreeForTwo
import Submission.Work.StemsB.fg_abelian_decomposition
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Pi6.EMZ.bocksteinLES
import Submission.Work.Pi6.EMZ.bocksteinSES
import Submission.Work.Pi6.EMZ.rankDual
import Submission.Work.Pi6.EMZ.loopShift
import Submission.Work.Pi6.EMZ.emExpTors
import Submission.Work.Pi6.EMZ.groupMod
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

AREA EMZ (pi6). Read REFS/NOTES_LEAD_PI6.md §7. Assume SerreRangeLES, EMMod2, EMOdd, EMExp.
Statement: for K(ℤ/2,4) models through N ≥ 12: H_6(−;ℤ) ≅ ZMod 2, H_7(−;ℤ) ≅ ZMod 2, rank H_8(−;𝔽₂) ≤ 2; for K(ℤ/2,5)
models through N ≥ 12: H_6(−;ℤ) = 0, H_7(−;ℤ) ≅ ZMod 2.
Route: H_i f.g. (Work.EMFG.emHomologyFG / Work.PiS.EMHomologyFG) + mod-p acyclicity for odd p (EMOdd) ⇒ finite 2-groups.
Range isos from SerreRangeLES (ℤ) applied to the path fibration of K_{n+1} (total contractible, fibre = loops = K_n
through N−1): H_6(K₄) ≅ H_5(K₃), H_7(K₅) ≅ H_6(K₄), H_6(K₅) ≅ H_5(K₄) ≅ H_4(K₃).
Mod-2 ranks via duality (kronH_bijective_field) and the Bockstein sequence 0 → H_n/2 → H_n(−;𝔽₂) → H_{n−1}[2] → 0:
K₃: H_3 = ℤ/2 (Hurewicz), rank H^4 ≤ 1 ⇒ H_4 = 0; rank H^5 ≤ 1 and H_4 = 0 ⇒ H_5 cyclic; EMExp ⇒ H_5 ≅ ℤ/2.
K₄: rank H^7 ≤ 2 and H_6[2] = ℤ/2 ⇒ H_7 cyclic; EMExp ⇒ H_7 ≅ ℤ/2; rank H_8(−;𝔽₂) = rank H^8 ≤ 2.
Lemma: a cyclic 2-group C with an element a, 2a = 0, a ∉ 2C, is ℤ/2.
Suggested children: Pi6/EMZ/bockstein (the homology Bockstein short exact sequence), Pi6/EMZ/finite2group,
Pi6/EMZ/rangeShift, Pi6/EMZ/k3table, Pi6/EMZ/k4table, Pi6/EMZ/k5table. Share the Bockstein lemma with HALG if it exists.
-/

/-! ## The development of this area

The vocabulary (`pH`, `torsP`, `BocksteinLES`) is in `Submission/Work/Pi6/EMZ/Defs.lean`; the
delegated pieces are `bocksteinLES` (the mod-`p` Bockstein long exact sequence), `bocksteinSES`
(the derived short exact sequence plus the cardinality identity), `rankDual` (duality: the rank of
homology is at most the rank of cohomology, and a rank bound over a finite field bounds the
cardinality), `loopShift` (the Serre range isomorphism `H_{i+1}(X) ≅ H_i(ΩX)`), `emExpTors` (the
`EMExp` exponent element as a `2`-torsion element which is not twice anything) and `groupMod` (the
finitely generated abelian group theory: divisibility and the exponent element force `0` or `ℤ/2`).
The tables `kThreeFacts` / `kFourFacts` and the assembly `emTableZMain` live in this file. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Pi6.EMZ

open Work.Pi6

noncomputable section

/-! ## Hurewicz helpers -/

theorem subsingleton_homology_of_conn {X : Type} [TopologicalSpace X] (x₀ : X) (j : ℕ)
    (hj : 2 ≤ j) (hconn : ∀ i : ℕ, i ≤ j → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Subsingleton (HR ℤ X j) := by
  have hb := Work.Stems.hurewicz_first_degree (Y := X) j hj x₀
    (fun i hi => hconn i (le_of_lt hi))
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hb.2 a
  obtain ⟨y, rfl⟩ := hb.2 b
  rw [(hconn j le_rfl).elim x y]

theorem card_homology_eq_card_homotopy {X : Type} [TopologicalSpace X] (x₀ : X) (m : ℕ)
    (hm : 2 ≤ m) (hconn : ∀ i : ℕ, i < m → Subsingleton (HomotopyGroup (Fin i) X x₀)) :
    Nat.card (HR ℤ X m) = Nat.card (HomotopyGroup (Fin m) X x₀) :=
  (Nat.card_congr (Equiv.ofBijective (Work.Stems.hurewiczMapN m (by omega) x₀)
    (Work.Stems.hurewicz_first_degree (Y := X) m hm x₀ hconn))).symm

theorem two_smul_eq_zero_of_exponent_two {X : Type} [TopologicalSpace X] (x₀ : X) (k : ℕ)
    (hk : 1 ≤ k) (hconn : ∀ i : ℕ, i < k + 1 → Subsingleton (HomotopyGroup (Fin i) X x₀))
    {A : Type} [AddCommGroup A] (hexp : ∀ a : A, 2 • a = 0)
    (h : Nonempty (HomotopyGroup (Fin (k + 1)) X x₀ ≃* Multiplicative A))
    (y : HR ℤ X (k + 1)) : 2 • y = 0 := by
  obtain ⟨e⟩ := h
  have hexpπ : ∀ z : HomotopyGroup (Fin (k + 1)) X x₀, z * z = 1 := by
    intro z
    refine e.injective ?_
    rw [map_mul, map_one]
    have hw : (e z).toAdd + (e z).toAdd = (0 : A) := by
      simpa [two_nsmul] using hexp ((e z).toAdd)
    have : (e z * e z).toAdd = (1 : Multiplicative A).toAdd := by
      rw [toAdd_mul]
      exact hw
    exact Multiplicative.toAdd.injective this
  have hb := Work.Stems.hurewicz_first_degree (Y := X) (k + 1) (by omega) x₀ hconn
  obtain ⟨x, hx⟩ := hb.2 y
  rw [← hx]
  have hkey : (2 : ℕ) • Work.Stems.hurewiczMapN (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) x₀ x =
      Work.Stems.hurewiczMapN (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) x₀ (x * x) := by
    rw [two_nsmul, Work.Stems.hurewiczMapN_mul k x₀ x x]
  rw [hkey, hexpπ x]
  exact Work.Stems.hurewiczMap_one k

/-! ## finiteness bridges -/

theorem finite_of_module_finite (R : Type) [Ring R] [Finite R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] : Finite M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact Finite.of_surjective f hf

theorem finite_of_rank_cohomology (𝕜 : Type) [Field 𝕜] [Fintype 𝕜] (X : Type) [TopologicalSpace X]
    (n r : ℕ) (h : Module.rank 𝕜 (Coh 𝕜 X n) ≤ r) : Finite (HR 𝕜 X n) := by
  haveI : Module.Free 𝕜 (HR 𝕜 X n) := Module.Free.of_divisionRing 𝕜 _
  have hle : Module.rank 𝕜 (HR 𝕜 X n) ≤ r := (rankDual.1 𝕜 X n).trans h
  have hlt : Module.rank 𝕜 (HR 𝕜 X n) < Cardinal.aleph0 :=
    lt_of_le_of_lt hle Cardinal.natCast_lt_aleph0
  haveI : Module.Finite 𝕜 (HR 𝕜 X n) := Module.rank_lt_aleph0_iff.mp hlt
  exact finite_of_module_finite 𝕜 _



/-! ## generic tools -/

/-- `2 • w = 0` in `ZMod 2`. -/
theorem zmod_two_two_smul (w : ZMod 2) : (2 : ℤ) • w = 0 := by
  fin_cases w <;> decide

/-- `2 • w = 0` in `ZMod 2`, `nsmul` form. -/
theorem zmod_two_two_nsmul (w : ZMod 2) : 2 • w = 0 := by
  fin_cases w <;> decide

/-- An abelian group additively isomorphic to `ZMod 2` has exponent dividing `2`. -/
theorem two_smul_eq_zero_of_addEquiv {G : Type} [AddCommGroup G] (e : G ≃+ ZMod 2) :
    ∀ y : G, 2 • y = 0 := by
  intro y
  apply e.injective
  rw [map_nsmul, map_zero]
  exact zmod_two_two_nsmul (e y)

/-- The `ℤ`-module structure on an abelian group is unique, so `Module.Finite` transfers between
any two `Module ℤ` structures. -/
theorem moduleFinite_canonical {G : Type} [AddCommGroup G] (m : Module ℤ G)
    (h : @Module.Finite ℤ G _ _ m) :
    @Module.Finite ℤ G _ _ (AddCommGroup.toIntModule G) := by
  rw [Subsingleton.elim m (AddCommGroup.toIntModule G)] at h
  exact h

/-- `Nat.card` of the full subgroup. -/
theorem natCard_torsP_eq_of_exponent_two {G : Type} [AddCommGroup G] (p : ℕ)
    (h : ∀ y : G, p • y = 0) : Nat.card ↥(torsP p G) = Nat.card G :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun x => mem_torsP'.mpr (h x))

/-- The `p`-torsion subgroup of a trivial group has one element. -/
theorem natCard_torsP_eq_one {G : Type} [AddCommGroup G] (p : ℕ) (h : Subsingleton G) :
    Nat.card ↥(torsP p G) = 1 := by
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (h.elim _ _)⟩, ⟨⟨0, ?_⟩⟩⟩
  rw [mem_torsP']
  simp

/-- A finite nonempty type of cardinality at most one has cardinality one. -/
theorem natCard_eq_one_of_le_one {α : Type} [Nonempty α] [Finite α] (h : Nat.card α ≤ 1) :
    Nat.card α = 1 := by
  have := Nat.card_pos (α := α)
  omega

/-- `a ∉ pH 2 G` in the `nsmul` form. -/
theorem not_mem_pH_two {G : Type} [AddCommGroup G] {a : G} :
    a ∉ pH 2 G ↔ ∀ b : G, 2 • b ≠ a := by
  rw [mem_pH']
  simp [eq_comm]

/-- **Bockstein, trivial middle term**: if `H_{n+1}(X;ℤ/p)` vanishes then so do `H_{n+1}(X;ℤ)/p`
and the `p`-torsion of `H_n(X;ℤ)`. -/
theorem trivial_quot_and_tors {X : Type} [TopologicalSpace X] (p : ℕ) (hp : p.Prime) (n : ℕ)
    (htriv : Subsingleton (HR (ZMod p) X (n + 1))) :
    Subsingleton (HR ℤ X (n + 1) ⧸ pH p (HR ℤ X (n + 1))) ∧
      Subsingleton (torsP p (HR ℤ X n)) := by
  obtain ⟨f, g, hf, hg, -, -⟩ := bocksteinSES p hp (bocksteinLES p hp) X n
  refine ⟨⟨fun a b => hf (Subsingleton.elim (f a) (f b))⟩, ⟨fun a b => ?_⟩⟩
  obtain ⟨a', ha'⟩ := hg a
  obtain ⟨b', hb'⟩ := hg b
  rw [← ha', ← hb', Subsingleton.elim a' b']

/-! ## the K(ℤ/2,3) table -/

theorem kThreeFacts (hM2 : EMMod2) (hO : EMOdd) (hXe : EMExp)
    {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ) (hpos : 0 < 3)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 hpos N X x₀) (hN : 10 ≤ N) :
    Subsingleton (HR ℤ X 4) ∧ Nonempty (HR ℤ X 5 ≃+ ZMod 2) := by
  have h2p : Nat.Prime 2 := Nat.prime_two
  have hfg : ∀ i : ℕ, i ≤ N - 1 → Module.Finite ℤ (HR ℤ X i) := by
    intro i hi
    have hEM := (Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo :
      Work.PiS.EMHomologyFG)
    have hX' : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) (N - 1 + 1) X x₀ := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
      exact hX
    exact hEM (ZMod 2) 3 (by norm_num) (N - 1) X x₀ hX' i hi
  have hπ3 : ∀ i : ℕ, i < 3 → Subsingleton (HomotopyGroup (Fin i) X x₀) :=
    fun i hi => hX.2 i (by omega) (Or.inl hi)
  have hcard3 : Nat.card (HR ℤ X 3) = 2 := by
    rw [card_homology_eq_card_homotopy x₀ 3 (by norm_num) hπ3]
    obtain ⟨e⟩ := hX.1
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_zmod]
  have hexp3 : ∀ y : HR ℤ X 3, 2 • y = 0 := by
    obtain ⟨e⟩ := (hX.1 : Nonempty (HomotopyGroup (Fin 3) X x₀ ≃* Multiplicative (ZMod 2)))
    exact two_smul_eq_zero_of_exponent_two x₀ 2 (by norm_num) hπ3 (fun a => zmod_two_two_smul a)
      ⟨e⟩
  have hcardT3 : Nat.card ↥(torsP 2 (HR ℤ X 3)) = 2 := by
    rw [natCard_torsP_eq_of_exponent_two 2 hexp3, hcard3]
  have hh4 := (hM2.2.1 X x₀ N hN hX).1
  have hh5 := (hM2.2.1 X x₀ N hN hX).2.1
  have hc4 : Nat.card (HR (ZMod 2) X 4) ≤ 2 := by
    simpa using rankDual.2 (ZMod 2) X 4 1 hh4
  have hc5 : Nat.card (HR (ZMod 2) X 5) ≤ 2 := by
    simpa using rankDual.2 (ZMod 2) X 5 1 hh5
  have hfin4 : Finite (HR (ZMod 2) X 4) := finite_of_rank_cohomology (ZMod 2) X 4 1 hh4
  have hfin5 : Finite (HR (ZMod 2) X 5) := finite_of_rank_cohomology (ZMod 2) X 5 1 hh5
  obtain ⟨f4, g4, hf4, -, -, hcard4⟩ := bocksteinSES 2 h2p (bocksteinLES 2 h2p) X 3
  haveI : Finite (HR ℤ X 4 ⧸ pH 2 (HR ℤ X 4)) := Finite.of_injective f4 hf4
  have hcard4' : Nat.card (HR (ZMod 2) X 4) =
      Nat.card (HR ℤ X 4 ⧸ pH 2 (HR ℤ X 4)) * Nat.card ↥(torsP 2 (HR ℤ X 3)) :=
    hcard4 hfin4
  have hquot2 : Subsingleton (HR ℤ X 4 ⧸ pH 2 (HR ℤ X 4)) := by
    have h1 : Nat.card (HR ℤ X 4 ⧸ pH 2 (HR ℤ X 4)) *
        Nat.card ↥(torsP 2 (HR ℤ X 3)) ≤ 2 := by
      rw [← hcard4']
      exact hc4
    rw [hcardT3] at h1
    have h2 : Nat.card (HR ℤ X 4 ⧸ pH 2 (HR ℤ X 4)) ≤ 1 := by
      have h3 : Nat.card (HR ℤ X 4 ⧸ pH 2 (HR ℤ X 4)) * 2 ≤ 1 * 2 := by simpa using h1
      exact Nat.le_of_mul_le_mul_right h3 (by norm_num : 0 < 2)
    exact (Nat.card_eq_one_iff_unique.mp (natCard_eq_one_of_le_one h2)).1
  have hdiv4 : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (HR ℤ X 4 ⧸ pH p (HR ℤ X 4)) := by
    intro p hp hp2
    exact (trivial_quot_and_tors p hp 3 (hO 3 (by norm_num) (by norm_num) X x₀ N hN hX p hp hp2 4
      (by norm_num) (by norm_num))).1
  have htor4 : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (torsP p (HR ℤ X 4)) := by
    intro p hp hp2
    exact (trivial_quot_and_tors p hp 4 (hO 3 (by norm_num) (by norm_num) X x₀ N hN hX p hp hp2 5
      (by norm_num) (by norm_num))).2
  have h4 : Subsingleton (HR ℤ X 4) :=
    groupMod.1 (HR ℤ X 4) (HR ℤ X 4).isModule (hfg 4 (by omega)) hquot2 hdiv4 htor4
  have hdiv5 : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (HR ℤ X 5 ⧸ pH p (HR ℤ X 5)) := by
    intro p hp hp2
    exact (trivial_quot_and_tors p hp 4 (hO 3 (by norm_num) (by norm_num) X x₀ N hN hX p hp hp2 5
      (by norm_num) (by norm_num))).1
  have htor5 : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (torsP p (HR ℤ X 5)) := by
    intro p hp hp2
    exact (trivial_quot_and_tors p hp 5 (hO 3 (by norm_num) (by norm_num) X x₀ N hN hX p hp hp2 6
      (by norm_num) (by norm_num))).2
  have hquot5 : Nat.card (HR ℤ X 5 ⧸ pH 2 (HR ℤ X 5)) ≤ 2 := by
    obtain ⟨f5, g5, hf5, -, -, hcard5⟩ := bocksteinSES 2 h2p (bocksteinLES 2 h2p) X 4
    have hcard5' : Nat.card (HR (ZMod 2) X 5) =
        Nat.card (HR ℤ X 5 ⧸ pH 2 (HR ℤ X 5)) * Nat.card ↥(torsP 2 (HR ℤ X 4)) :=
      hcard5 hfin5
    rw [natCard_torsP_eq_one 2 h4, mul_one] at hcard5'
    rw [← hcard5']
    exact hc5
  have ha5 : ∃ a : HR ℤ X 5, 2 • a = 0 ∧ ∀ b : HR ℤ X 5, 2 • b ≠ a := by
    obtain ⟨a, ha1, ha2⟩ := emExpTors hXe |>.1 X x₀ N hN hX
    exact ⟨a, mem_torsP'.mp ha1, not_mem_pH_two.mp ha2⟩
  have h5 : Nonempty (HR ℤ X 5 ≃+ ZMod 2) :=
    groupMod.2 (HR ℤ X 5) (HR ℤ X 5).isModule (hfg 5 (by omega)) hquot5 hdiv5 htor5 ha5
  exact ⟨h4, h5⟩

/-! ## the K(ℤ/2,4) table -/

theorem kFourFacts (hR : SerreRangeLES) (hM2 : EMMod2) (hO : EMOdd) (hXe : EMExp)
    {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ) (hpos : 0 < 4)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 hpos N X x₀) (hN : 11 ≤ N) :
    Subsingleton (HR ℤ X 5) ∧ Nonempty (HR ℤ X 6 ≃+ ZMod 2) := by
  have hloop : Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) (N - 1)
      (Path x₀ x₀) (Path.refl x₀) :=
    Work.Stems.isEMSpaceUpTo_loop (A := ZMod 2) (k := 3) (M := N) (by norm_num) x₀ hX
  obtain ⟨hz4, hz5⟩ := kThreeFacts hM2 hO hXe (Path.refl x₀) (N - 1) (by norm_num) hloop
    (by omega)
  obtain ⟨e5⟩ := loopShift hR X x₀ 4 N 4 (by norm_num) hX (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨e6⟩ := loopShift hR X x₀ 4 N 5 (by norm_num) hX (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨⟨fun a b => e5.injective (hz4.elim (e5 a) (e5 b))⟩, ?_⟩
  exact ⟨e6.toAddEquiv.trans hz5.some⟩



/-! ## the main theorem -/

theorem emTableZMain (hR : SerreRangeLES) (hM2 : EMMod2) (hO : EMOdd) (hXe : EMExp) :
    EMTableZ := by
  have h2p : Nat.Prime 2 := Nat.prime_two
  have hfg : ∀ {X : Type} [TopologicalSpace X] (x₀ : X) (m N : ℕ) (hm : 2 ≤ m) (hN : 1 ≤ N),
      Work.Serre.IsEMSpaceUpTo (ZMod 2) m (by omega) N X x₀ → ∀ i : ℕ, i ≤ N - 1 →
        Module.Finite ℤ (HR ℤ X i) := by
    intro X _ x₀ m N hm hN hX i hi
    have hEM := (Work.EMFG.emHomologyFG Work.SSS.serreFGThreeForTwo : Work.PiS.EMHomologyFG)
    have hX' : Work.Serre.IsEMSpaceUpTo (ZMod 2) m (by omega) (N - 1 + 1) X x₀ := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
      exact hX
    exact hEM (ZMod 2) m hm (N - 1) X x₀ hX' i hi
  refine ⟨?_, ?_⟩
  · intro X _ x₀ N hN hX
    have hN10 : 10 ≤ N := by omega
    have hN11 : 11 ≤ N := by omega
    obtain ⟨hz5, hz6⟩ := kFourFacts hR hM2 hO hXe x₀ N (by norm_num) hX hN11
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨e⟩ := hz6
      exact ⟨e.toIntLinearEquiv⟩
    · have hh7 := (hM2.2.2 X x₀ N hN10 hX).1
      have hc7 : Nat.card (HR (ZMod 2) X 7) ≤ 4 := by
        simpa using rankDual.2 (ZMod 2) X 7 2 hh7
      have hfin7 : Finite (HR (ZMod 2) X 7) := finite_of_rank_cohomology (ZMod 2) X 7 2 hh7
      obtain ⟨e6⟩ := hz6
      have hexp6 : ∀ y : HR ℤ X 6, 2 • y = 0 := two_smul_eq_zero_of_addEquiv e6
      have hcardT6 : Nat.card ↥(torsP 2 (HR ℤ X 6)) = 2 := by
        rw [natCard_torsP_eq_of_exponent_two 2 hexp6]
        rw [Nat.card_congr e6.toEquiv, Nat.card_zmod]
      obtain ⟨f7, g7, hf7, -, -, hcard7⟩ := bocksteinSES 2 h2p (bocksteinLES 2 h2p) X 6
      haveI : Finite (HR ℤ X 7 ⧸ pH 2 (HR ℤ X 7)) := Finite.of_injective f7 hf7
      have hcard7' : Nat.card (HR (ZMod 2) X 7) =
          Nat.card (HR ℤ X 7 ⧸ pH 2 (HR ℤ X 7)) * Nat.card ↥(torsP 2 (HR ℤ X 6)) :=
        hcard7 hfin7
      have hq7 : Nat.card (HR ℤ X 7 ⧸ pH 2 (HR ℤ X 7)) ≤ 2 := by
        have h1 : Nat.card (HR ℤ X 7 ⧸ pH 2 (HR ℤ X 7)) *
            Nat.card ↥(torsP 2 (HR ℤ X 6)) ≤ 4 := by
          rw [← hcard7']
          exact hc7
        rw [hcardT6] at h1
        have h3 : Nat.card (HR ℤ X 7 ⧸ pH 2 (HR ℤ X 7)) * 2 ≤ 2 * 2 := by simpa using h1
        exact Nat.le_of_mul_le_mul_right h3 (by norm_num : 0 < 2)
      have hdiv7 : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (HR ℤ X 7 ⧸ pH p (HR ℤ X 7)) := by
        intro p hp hp2
        exact (trivial_quot_and_tors p hp 6
          (hO 4 (by norm_num) (by norm_num) X x₀ N hN10 hX p hp hp2 7 (by norm_num)
            (by norm_num))).1
      have htor7 : ∀ p : ℕ, p.Prime → p ≠ 2 → Subsingleton (torsP p (HR ℤ X 7)) := by
        intro p hp hp2
        exact (trivial_quot_and_tors p hp 7
          (hO 4 (by norm_num) (by norm_num) X x₀ N hN10 hX p hp hp2 8 (by norm_num)
            (by norm_num))).2
      have ha7 : ∃ a : HR ℤ X 7, 2 • a = 0 ∧ ∀ b : HR ℤ X 7, 2 • b ≠ a := by
        obtain ⟨a, ha1, ha2⟩ := emExpTors hXe |>.2 X x₀ N hN hX
        exact ⟨a, mem_torsP'.mp ha1, not_mem_pH_two.mp ha2⟩
      obtain ⟨e⟩ := groupMod.2 (HR ℤ X 7) (HR ℤ X 7).isModule
        (hfg x₀ 4 N (by norm_num) (by omega) hX 7 (by omega)) hq7 hdiv7 htor7 ha7
      exact ⟨e.toIntLinearEquiv⟩
    · exact (rankDual.1 (ZMod 2) X 8).trans (hM2.2.2 X x₀ N hN10 hX).2
  · intro X _ x₀ N hN hX
    have hloop : Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) (N - 1)
        (Path x₀ x₀) (Path.refl x₀) :=
      Work.Stems.isEMSpaceUpTo_loop (A := ZMod 2) (k := 4) (M := N) (by norm_num) x₀ hX
    obtain ⟨hz5, hz6⟩ := kFourFacts hR hM2 hO hXe (Path.refl x₀) (N - 1) (by norm_num)
      hloop (by omega)
    obtain ⟨e6⟩ := loopShift hR X x₀ 5 N 5 (by norm_num) hX (by norm_num) (by norm_num)
      (by norm_num)
    obtain ⟨e7⟩ := loopShift hR X x₀ 5 N 6 (by norm_num) hX (by norm_num) (by norm_num)
      (by norm_num)
    refine ⟨⟨fun a b => e6.injective (hz5.elim (e6 a) (e6 b))⟩, ?_⟩
    obtain ⟨e⟩ := hz6
    exact ⟨(e7.toAddEquiv.trans e).toIntLinearEquiv⟩

end

end Work.Pi6.EMZ

namespace Work.Pi6

/-- **AREA EMZ.**  The integral tables for `K(ℤ/2,4)` and `K(ℤ/2,5)` range models, from the
Bockstein long exact sequence, the mod-2 duality bounds (`EMMod2`), the odd-primary acyclicity
(`EMOdd`) and the exponent input (`EMExp`). -/
theorem emTableZ (hR : Work.Pi6.SerreRangeLES) (hM2 : Work.Pi6.EMMod2) (hO : Work.Pi6.EMOdd)
    (hX : Work.Pi6.EMExp) : Work.Pi6.EMTableZ :=
  Work.Pi6.EMZ.emTableZMain hR hM2 hO hX

end Work.Pi6
