import Mathlib
import Submission.Work.HP.GonLib
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.Lat.prim_bezout
import Submission.Work.HP.ball_count_schmidt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section
open Finset
open scoped BigOperators
open Module

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The set whose infimum defines `latMin`. -/
def latMinSet {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) : Set ℝ :=
  {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
    ∀ j, ‖Φ (fun k => (f j k : ℝ))‖ ≤ r}

lemma latMin_eq_sInf {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) :
    latMin Φ i = sInf (latMinSet Φ i) := rfl

lemma latMin_nonneg {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) : 0 ≤ latMin Φ i := by
  rw [latMin_eq_sInf]
  by_cases h : (latMinSet Φ i).Nonempty
  · exact le_csInf h fun x hx => hx.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

lemma latMinSet_mono {R : ℕ} (Φ : LatMap (ι := ι) R) {i j : ℕ} (hij : i ≤ j) :
    latMinSet Φ j ⊆ latMinSet Φ i := by
  rintro r ⟨hr0, f, hf, hfr⟩
  exact ⟨hr0, fun k => f (Fin.castLE hij k),
    hf.comp (Fin.castLE hij) (Fin.castLE_injective hij), fun k => hfr _⟩

lemma latMinSet_nonempty {R i : ℕ} (Φ : LatMap (ι := ι) R) (hi : i ≤ R) :
    (latMinSet Φ i).Nonempty := by
  classical
  refine ⟨∑ j : Fin i, ‖Φ (fun k => ((Pi.single (Fin.castLE hi j) (1 : ℤ) : Fin R → ℤ) k : ℝ))‖,
    Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j =>
      (Pi.single (Fin.castLE hi j) (1 : ℤ) : Fin R → ℤ), ?_, ?_⟩
  · have hb : LinearIndependent ℤ (fun i : Fin R => (Pi.single i (1 : ℤ) : Fin R → ℤ)) :=
      Pi.linearIndependent_single_one (Fin R) ℤ
    exact hb.comp (Fin.castLE hi) (Fin.castLE_injective hi)
  · intro j
    exact Finset.single_le_sum
      (f := fun j : Fin i => ‖Φ (fun k => ((Pi.single (Fin.castLE hi j) (1 : ℤ) : Fin R → ℤ) k : ℝ))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

lemma latMin_mono {R : ℕ} (Φ : LatMap (ι := ι) R) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ R) :
    latMin Φ i ≤ latMin Φ j := by
  rw [latMin_eq_sInf, latMin_eq_sInf]
  exact le_csInf (latMinSet_nonempty Φ hj) fun r hr => csInf_le
    ⟨0, fun x hx => hx.1⟩ (latMinSet_mono Φ hij hr)

lemma latMin_witness {R : ℕ} (Φ : LatMap (ι := ι) R) {i : ℕ} (hi : i ≤ R) {ρ : ℝ}
    (hρ : latMin Φ i < ρ) :
    ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ j, ‖Φ (fun k => (f j k : ℝ))‖ ≤ ρ := by
  rw [latMin_eq_sInf] at hρ
  obtain ⟨s, ⟨-, f, hfli, hfs⟩, hsρ⟩ := exists_lt_of_csInf_lt (latMinSet_nonempty Φ hi) hρ
  exact ⟨f, hfli, fun j => (hfs j).trans hsρ.le⟩

lemma latMin_le_of_forall_eps {R : ℕ} (Φ : LatMap (ι := ι) R) {i : ℕ} {a : ℝ}
    (ha : 0 ≤ a)
    (h : ∀ ε > 0, ∃ f : Fin i → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ j, ‖Φ (fun k => (f j k : ℝ))‖ ≤ a + ε) :
    latMin Φ i ≤ a := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [latMin_eq_sInf]
  refine csInf_le ⟨0, fun x hx => hx.1⟩ ⟨by linarith, ?_⟩
  exact (h ε hε).imp fun f hf => ⟨hf.1, fun j => hf.2 j⟩

/-- Nearest integer. -/
lemma exists_int_close (t : ℝ) : ∃ k : ℤ, |t - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌈t - 1 / 2⌉, ?_⟩
  have h1 : t - 1 / 2 ≤ ((⌈t - 1 / 2⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h2 : ((⌈t - 1 / 2⌉ : ℤ) : ℝ) < t - 1 / 2 + 1 := Int.ceil_lt_add_one _
  rw [abs_le]
  constructor <;> linarith

/-- Bézout functional together with a `ℤ`-complement basis. -/
lemma prim_compl_data (n : ℕ) (u : Fin (n + 1) → ℤ) (hu : IsPrim u) :
    ∃ (φ : (Fin (n + 1) → ℤ) →ₗ[ℤ] ℤ) (v : Fin n → (Fin (n + 1) → ℤ)),
      φ u = 1 ∧ Function.Bijective (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • v i) := by
  classical
  obtain ⟨lam, hlam⟩ := Work.HP.Lat.prim_bezout u hu
  let φ : (Fin (n + 1) → ℤ) →ₗ[ℤ] ℤ := Fintype.linearCombination ℤ lam
  have hφu : φ u = 1 := by
    rw [Fintype.linearCombination_apply]
    simp only [smul_eq_mul]
    rw [← hlam]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  obtain ⟨nK, bK⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin (n + 1))) φ.ker
  have hnK : nK = n := by
    have h1 : Module.finrank ℤ ↥(φ.ker) = nK := by
      rw [Module.finrank_eq_card_basis bK]; simp
    have h2 : Module.finrank ℤ ((Fin (n + 1) → ℤ) ⧸ φ.ker) + Module.finrank ℤ ↥(φ.ker)
        = Module.finrank ℤ (Fin (n + 1) → ℤ) := Submodule.finrank_quotient_add_finrank φ.ker
    have h3 : Module.finrank ℤ ((Fin (n + 1) → ℤ) ⧸ φ.ker) = 1 := by
      rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange φ)]
      have hrange : φ.range = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro x
        have hx : x = φ (x • u) := by rw [map_smul, hφu, smul_eq_mul, mul_one]
        rw [hx]; exact LinearMap.mem_range_self φ _
      rw [hrange, LinearEquiv.finrank_eq (Submodule.topEquiv : (⊤ : Submodule ℤ ℤ) ≃ₗ[ℤ] ℤ),
        Module.finrank_self]
    have h4 : Module.finrank ℤ (Fin (n + 1) → ℤ) = n + 1 := by
      rw [Module.finrank_eq_card_basis (Pi.basisFun ℤ (Fin (n + 1)))]; simp
    omega
  let bK' : Module.Basis (Fin n) ℤ φ.ker := bK.reindex (finCongr hnK)
  let v : Fin n → (Fin (n + 1) → ℤ) := fun i => ((bK' i : φ.ker) : Fin (n + 1) → ℤ)
  have hvker : ∀ i, φ (v i) = 0 := fun i => (bK' i).2
  have hvLI : LinearIndependent ℤ v :=
    (bK'.linearIndependent).map' (Submodule.subtype φ.ker) (Submodule.ker_subtype φ.ker)
  have hvspan : Submodule.span ℤ (Set.range v) = φ.ker := by
    have h2 : Set.range v = Submodule.subtype φ.ker '' Set.range bK' := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨bK' i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    rw [h2, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  refine ⟨φ, v, hφu, ?_, ?_⟩
  · rintro ⟨a, c⟩ ⟨a', c'⟩ h
    have hφ := congrArg φ h
    simp only [map_add, map_smul, map_sum, hφu, hvker, smul_eq_mul, mul_one, smul_zero,
      Finset.sum_const_zero, add_zero] at hφ
    have ha : a = a' := by simpa using hφ
    refine Prod.ext ha ?_
    have hsum : ∑ i, c i • v i = ∑ i, c' i • v i := by
      have := h
      rw [← ha] at this
      exact add_left_cancel this
    have hzero : ∑ i, (c - c') i • v i = 0 := by
      rw [show (fun i => (c - c') i • v i) = (fun i => c i • v i - c' i • v i) from by
        funext i; rw [Pi.sub_apply, sub_smul]]
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    funext i
    have hci := (Fintype.linearIndependent_iff.mp hvLI) (c - c') hzero i
    have : c i - c' i = 0 := hci
    exact sub_eq_zero.mp this
  · intro x
    have hxmem : x - φ x • u ∈ Submodule.span ℤ (Set.range v) := by
      rw [hvspan, LinearMap.mem_ker]
      simp only [map_sub, map_smul, hφu, smul_eq_mul, mul_one, sub_self]
    rw [hvspan] at hxmem
    set y : φ.ker := ⟨x - φ x • u, hxmem⟩ with hy
    refine ⟨(φ x, bK'.repr y), ?_⟩
    have hrepr : ∑ i, (bK'.repr y) i • v i = x - φ x • u := by
      have hs := congrArg (fun z : φ.ker => (z : Fin (n + 1) → ℤ)) (Module.Basis.sum_repr bK' y)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, v] using hs
    show (φ x) • u + ∑ i, (bK'.repr y) i • v i = x
    rw [hrepr, add_sub_cancel]

/-! ## 2. Independence lemmas -/

/-- Extraction of an independent subfamily of maximal size from a spanning family. -/
lemma exists_subfamily_linind {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {m : ℕ} (z : Fin m → V)
    (h : Submodule.span K (Set.range z) = ⊤) :
    ∃ f : Fin (Module.finrank K V) → Fin m, Function.Injective f ∧ LinearIndependent K (z ∘ f) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K z
  haveI : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = Module.finrank K V := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hspan]; exact le_of_eq h.symm))]
  refine ⟨a ∘ (Fintype.equivFin κ).symm ∘ (finCongr hcard).symm, ?_, ?_⟩
  · exact ha.comp (Function.Injective.comp (Fintype.equivFin κ).symm.injective
      (finCongr hcard).symm.injective)
  · have hcomp : z ∘ (a ∘ (Fintype.equivFin κ).symm ∘ (finCongr hcard).symm)
      = (z ∘ a) ∘ ((Fintype.equivFin κ).symm ∘ (finCongr hcard).symm) := rfl
    rw [hcomp]
    exact hli.comp _ (Function.Injective.comp (Fintype.equivFin κ).symm.injective
      (finCongr hcard).symm.injective)

/-- Integer square vectors that are `ℤ`-linearly independent are `ℝ`-linearly independent. -/
lemma linind_int_to_real {m : ℕ} {w : Fin m → (Fin m → ℤ)} (h : LinearIndependent ℤ w) :
    LinearIndependent ℝ (fun i : Fin m => (fun k : Fin m => ((w i k : ℤ) : ℝ))) := by
  let f : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℚ) :=
    { toFun := fun v k => ((v k : ℤ) : ℚ)
      map_add' := fun u v => by ext k; simp
      map_smul' := fun n v => by ext k; simp }
  have hker : f.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    funext k
    have := congrFun huv k
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact_mod_cast this
  have hcoe : LinearIndependent ℤ (fun i : Fin m => (fun k : Fin m => ((w i k : ℤ) : ℚ))) :=
    h.map' f hker
  have hQ : LinearIndependent ℚ (fun i : Fin m => (fun k : Fin m => ((w i k : ℤ) : ℚ))) :=
    LinearIndependent.localization ℚ (nonZeroDivisors ℤ) hcoe
  set wQ : Fin m → (Fin m → ℚ) := fun i k => ((w i k : ℤ) : ℚ) with hwQ
  set wR : Fin m → (Fin m → ℝ) := fun i k => ((w i k : ℤ) : ℝ) with hwR
  have hspanQ : Submodule.span ℚ (Set.range wQ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_eq_card_basis (Module.Basis.span hQ),
      Module.finrank_eq_card_basis (Pi.basisFun ℚ (Fin m))]
  let j : (Fin m → ℚ) →ₗ[ℚ] (Fin m → ℝ) :=
    { toFun := fun v k => ((v k : ℚ) : ℝ)
      map_add' := fun u v => by ext k; simp
      map_smul' := fun a v => by ext k; simp [Pi.smul_apply, Algebra.smul_def] }
  have hmap : Submodule.map j (Submodule.span ℚ (Set.range wQ)) =
      Submodule.span ℚ (Set.range wR) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨wQ i, ⟨i, rfl⟩, rfl⟩
  have hspanR : Submodule.span ℝ (Set.range wR) = ⊤ := by
    rw [eq_top_iff, ← Module.Basis.span_eq (Pi.basisFun ℝ (Fin m)), Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Pi.basisFun_apply]
    have hmem : (Pi.single k (1 : ℝ) : Fin m → ℝ) ∈ Submodule.span ℚ (Set.range wR) := by
      rw [← hmap, hspanQ]
      refine ⟨(Pi.single k (1 : ℚ) : Fin m → ℚ), trivial, ?_⟩
      ext l
      by_cases hl : l = k <;> simp [j, hl]
    have hle : Submodule.span ℚ (Set.range wR) ≤
        (Submodule.span ℝ (Set.range wR)).restrictScalars ℚ :=
      Submodule.span_le.mpr (by intro x hx; exact Submodule.subset_span hx)
    exact hle hmem
  rw [linearIndependent_iff_card_eq_finrank_span]
  rw [Set.finrank, hspanR]
  rw [show Module.finrank ℝ (⊤ : Submodule ℝ (Fin m → ℝ)) = m from by
    rw [LinearEquiv.finrank_eq (Submodule.topEquiv : (⊤ : Submodule ℝ (Fin m → ℝ)) ≃ₗ[ℝ] (Fin m → ℝ)),
      Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin m))]
    simp]
  simp

/-! ## 3. The main induction -/

lemma sqrt_sq_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  have h1 : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((a + b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = a + b := Real.sqrt_sq (by linarith)

/-- **Main induction.** -/
theorem exists_short_basis_aux (R : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : LatMap (ι := ι) R), Function.Injective Φ →
      ∃ e : Module.Basis (Fin R) ℤ (Fin R → ℤ),
        ∑ i, ‖Φ (fun k => (e i k : ℝ))‖ ≤ C * latMin Φ R := by
  induction R using Nat.strong_induction_on with
  | h R ih =>
    rcases Nat.eq_zero_or_pos R with h0 | hpos
    · subst h0
      refine ⟨1, one_pos, fun Φ _ => ⟨Pi.basisFun ℤ (Fin 0), ?_⟩⟩
      have hzero : (∑ i : Fin 0, ‖Φ (fun k => ((Pi.basisFun ℤ (Fin 0) i) k : ℝ))‖) = 0 := by simp
      rw [hzero, one_mul]
      exact latMin_nonneg Φ 0
    · obtain ⟨n, rfl⟩ : ∃ n, R = n + 1 := ⟨R - 1, by omega⟩
      obtain ⟨C', hC'pos, hC'⟩ := ih n (by omega)
      refine ⟨1 + C' + (n : ℝ) / 2, by positivity, fun Φ hΦ => ?_⟩
      obtain ⟨u, hu0, huprim, hu1⟩ := lat_min_attained (R := n + 1) (by omega) Φ hΦ
      obtain ⟨φ, v, hφu, hvBij⟩ := prim_compl_data n u huprim
      have hwli : LinearIndependent ℤ (Fin.cons u v) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hc' : (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • v i)
            (c 0, fun i => c i.succ)
            = (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • v i) (0, 0) := by
          have h := hc
          rw [Fin.sum_univ_succ] at h
          simpa using h
        have hinj := hvBij.1 hc'
        have h0 : c 0 = 0 := congrArg Prod.fst hinj
        have hsucc : (fun i : Fin n => c i.succ) = 0 := congrArg Prod.snd hinj
        intro i
        obtain ⟨m, hm⟩ := i
        rcases m with _ | m
        · have hi : (⟨0, hm⟩ : Fin (n + 1)) = 0 := rfl
          rw [hi]; exact h0
        · have hi : (⟨m + 1, hm⟩ : Fin (n + 1)) = (⟨m, by omega⟩ : Fin n).succ := rfl
          rw [hi]; exact congrFun hsucc ⟨m, by omega⟩
      have hwRli : LinearIndependent ℝ (fun i : Fin (n + 1) =>
          (fun k : Fin (n + 1) =>
            (((Fin.cons u v : Fin (n + 1) → (Fin (n + 1) → ℤ)) i k : ℤ) : ℝ))) :=
        linind_int_to_real (m := n + 1) hwli
      set uE : EuclideanSpace ℝ ι := Φ (fun k => (u k : ℝ)) with huE
      have huE0 : uE ≠ 0 := by
        intro h
        have huv : (fun k => (u k : ℝ)) = 0 := hΦ (by rw [← huE, h, map_zero])
        exact hu0 (funext fun k => by
          have h1 := congrFun huv k
          simp only [Pi.zero_apply] at h1
          exact_mod_cast h1)
      set π : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι := projU uE with hπ
      have hπu : π uE = 0 := by rw [hπ]; exact projU_self_eq_zero uE huE0
      let L : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
        Fintype.linearCombination ℝ (fun i : Fin n => (fun k : Fin (n + 1) => ((v i k : ℤ) : ℝ)))
      let Ψ : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι := π.comp (Φ.comp L)
      have hL : ∀ y : Fin n → ℝ, L y = fun k => ∑ i, y i * ((v i k : ℤ) : ℝ) := by
        intro y; ext k
        simp [L, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hΨapply : ∀ y : Fin n → ℝ,
          Ψ y = π (Φ (fun k => ∑ i, y i * ((v i k : ℤ) : ℝ))) := by
        intro y
        show π (Φ (L y)) = _
        rw [hL y]
      have hΨinj : Function.Injective Ψ := by
        intro y y' hyy
        have hπ0 : π (Φ (fun k => ∑ i, (y i - y' i) * ((v i k : ℤ) : ℝ))) = 0 := by
          have hsub : (fun k => ∑ i, (y i - y' i) * ((v i k : ℤ) : ℝ))
              = (fun k => ∑ i, y i * ((v i k : ℤ) : ℝ))
                - (fun k => ∑ i, y' i * ((v i k : ℤ) : ℝ)) := by
            ext k
            simp only [Pi.sub_apply]
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun i _ => by ring)
          simp only [hsub, Φ.map_sub, π.map_sub, ← hΨapply y, ← hΨapply y', hyy, sub_self]
        have hspanmem := (projU_eq_zero_iff uE huE0
          (Φ (fun k => ∑ i, (y i - y' i) * ((v i k : ℤ) : ℝ)))).mp hπ0
        obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hspanmem
        clear hspanmem
        have hw : (fun k => ∑ i, (y i - y' i) * ((v i k : ℤ) : ℝ)) = cc • (fun k => (u k : ℝ)) := by
          apply hΦ
          rw [← hcc, Φ.map_smul]
        have hd : ∑ i : Fin (n + 1), (Fin.cons cc (fun i => -(y i - y' i)) : Fin (n + 1) → ℝ) i
            • (fun k : Fin (n + 1) =>
              (((Fin.cons u v : Fin (n + 1) → (Fin (n + 1) → ℤ)) i k : ℤ) : ℝ)) = 0 := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          have hveceq : (∑ i : Fin n, (y i - y' i) • (fun k => ((v i k : ℤ) : ℝ)))
              = cc • (fun k => (u k : ℝ)) := by
            ext k
            simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hw k
          rw [← hveceq, ← Finset.sum_add_distrib]
          apply Finset.sum_eq_zero
          intro i _
          rw [← add_smul, add_neg_cancel, zero_smul]
        have hz := (Fintype.linearIndependent_iff.mp hwRli)
          (Fin.cons cc (fun i => -(y i - y' i))) hd
        funext i
        have hzi := hz i.succ
        simp only [Fin.cons_succ] at hzi
        linarith
      have hΨlat : latMin Ψ n ≤ latMin Φ (n + 1) := by
        refine latMin_le_of_forall_eps Ψ (latMin_nonneg Φ (n + 1)) fun ε hε => ?_
        obtain ⟨x, hxli, hxn⟩ := latMin_witness Φ (le_refl (n + 1))
          (lt_add_of_pos_right _ hε)
        choose cc hcc using fun j => hvBij.2 (x j)
        set xR : Fin (n + 1) → (Fin (n + 1) → ℝ) := fun j k => ((x j k : ℤ) : ℝ) with hxR
        set bR : Fin (n + 1) → (Fin n → ℝ) := fun j i => (((cc j).2 i : ℤ) : ℝ) with hbR
        have hxspan : Submodule.span ℝ (Set.range xR) = ⊤ := by
          have hli : LinearIndependent ℝ xR := by
            have h := linind_int_to_real hxli
            rwa [← hxR] at h
          have hcard := linearIndependent_iff_card_eq_finrank_span.mp hli
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [← Set.finrank, ← hcard, Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin (n + 1)))]
        have hbΨ : ∀ j : Fin (n + 1), Ψ (bR j) = π (Φ (xR j)) := by
          intro j
          have hxdec : xR j = ((cc j).1 : ℝ) • (fun k => (u k : ℝ)) + L (bR j) := by
            show (fun k => ((x j k : ℤ) : ℝ)) = _
            rw [← hcc j, hbR]
            ext k
            simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, L,
              Fintype.linearCombination_apply] <;> push_cast <;> ring_nf
          rw [hxdec]
          show π (Φ (L (bR j))) =
            π (Φ (((cc j).1 : ℝ) • (fun k => (u k : ℝ)) + L (bR j)))
          rw [Φ.map_add, Φ.map_smul, ← huE]
          rw [π.map_add, π.map_smul, hπu, smul_zero, zero_add]
        have hspb : Submodule.span ℝ (Set.range bR) = ⊤ := by
          rw [Submodule.eq_top_iff']
          intro y
          have hLy : L y ∈ Submodule.span ℝ (Set.range xR) := by rw [hxspan]; trivial
          have h1 : Ψ y ∈ Submodule.span ℝ (Set.range (fun j => Ψ (bR j))) := by
            have h3 : π (Φ (L y)) ∈ Submodule.map (π.comp Φ) (Submodule.span ℝ (Set.range xR)) :=
              Submodule.mem_map_of_mem hLy
            rw [Submodule.map_span] at h3
            have hset : (π.comp Φ) '' Set.range xR = Set.range (fun j => Ψ (bR j)) := by
              rw [← Set.range_comp]
              congr 1
              funext j
              exact (hbΨ j).symm
            rwa [hset] at h3
          have h4 : Submodule.span ℝ (Set.range (fun j => Ψ (bR j)))
              = Submodule.map Ψ (Submodule.span ℝ (Set.range bR)) := by
            rw [Submodule.map_span]
            congr 1
            ext z
            constructor
            · rintro ⟨j, rfl⟩; exact ⟨bR j, ⟨j, rfl⟩, rfl⟩
            · rintro ⟨x', ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
          rw [h4] at h1
          obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp h1
          have hzy' : z = y := hΨinj hzy
          rwa [← hzy']
        obtain ⟨f, hf, hfli⟩ := exists_subfamily_linind (K := ℝ) bR hspb
        have hcardf : Module.finrank ℝ (Fin n → ℝ) = n := by
          rw [Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin n))]; simp
        let g : Fin n → Fin (n + 1) := f ∘ (finCongr hcardf).symm
        refine ⟨fun i => (cc (g i)).2, ?_, fun i => ?_⟩
        · rw [Fintype.linearIndependent_iff]
          intro c hc
          have hli2 : LinearIndependent ℝ (fun k : Fin n => bR (g k)) :=
            hfli.comp (finCongr hcardf).symm (finCongr hcardf).symm.injective
          have hcR : ∑ k : Fin n, ((c k : ℤ) : ℝ) • bR (g k) = 0 := by
            ext i
            have h := congrFun (congrArg (fun z : Fin n → ℤ => fun i : Fin n => (z i : ℝ)) hc) i
            have h' : ((∑ k, c k * (cc (g k)).2 i : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by
              simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hbR] using h
            simp only [Int.cast_zero] at h'
            push_cast at h'
            simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hbR] using h'
          intro k
          have hk := (Fintype.linearIndependent_iff.mp hli2) (fun k => ((c k : ℤ) : ℝ)) hcR k
          exact_mod_cast hk
        · have hxg := hxn (g i)
          have h1 : ‖Ψ (fun k => ((cc (g i)).2 k : ℝ))‖ = ‖π (Φ (xR (g i)))‖ := by
            rw [show (fun k => ((cc (g i)).2 k : ℝ)) = bR (g i) from rfl, hbΨ (g i)]
          rw [h1]
          exact (norm_projU_le uE (Φ (xR (g i)))).trans hxg
      obtain ⟨e', he'⟩ := hC' Ψ hΨinj
      choose kk hkk using fun i : Fin n =>
        exists_int_close (inner ℝ (Φ (fun k => ∑ j, (e' i j) * ((v j k : ℤ) : ℝ))) uE / ‖uE‖ ^ 2)
      set X : Fin n → (Fin (n + 1) → ℤ) :=
        fun i => (∑ j, (e' i j) • v j) - kk i • u with hX
      have hXbound : ∀ i : Fin n,
          ‖Φ (fun k => (X i k : ℝ))‖ ≤ ‖Ψ (fun k => (e' i k : ℝ))‖ + ‖uE‖ / 2 := by
        intro i
        set zR : Fin (n + 1) → ℝ := fun k => ∑ j, (e' i j) * ((v j k : ℤ) : ℝ) with hzR
        have hzX : (fun k => (X i k : ℝ)) = zR - ((kk i : ℝ)) • (fun k => (u k : ℝ)) := by
          rw [hX, hzR]
          ext k
          simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          push_cast
          ring_nf
        have hπz : projU uE (Φ zR) = Ψ (fun k => (e' i k : ℝ)) := by
          rw [hΨapply]
        have hsq : ‖Φ (fun k => (X i k : ℝ))‖ ^ 2
            ≤ ‖Ψ (fun k => (e' i k : ℝ))‖ ^ 2 + (‖uE‖ / 2) ^ 2 := by
          have hXeq : Φ (fun k => (X i k : ℝ)) = Φ zR - ((kk i : ℝ)) • uE := by
            rw [hzX]
            simp only [Φ.map_sub, Φ.map_smul, ← huE]
          rw [hXeq]
          have h1 : ‖Φ zR - ((kk i : ℝ)) • uE‖ ^ 2
              = ‖Ψ (fun k => (e' i k : ℝ))‖ ^ 2
                + (inner ℝ (Φ zR) uE / ‖uE‖ ^ 2 - (kk i : ℝ)) ^ 2 * ‖uE‖ ^ 2 := by
            rw [sub_eq_add_neg, ← neg_smul, norm_sq_add_smul uE (-(kk i : ℝ)) (Φ zR), hπz]
            ring
          rw [h1]
          have hhalf : (inner ℝ (Φ zR) uE / ‖uE‖ ^ 2 - (kk i : ℝ)) ^ 2 * ‖uE‖ ^ 2
              ≤ (1 / 2 : ℝ) ^ 2 * ‖uE‖ ^ 2 := by
            have hk := hkk i
            have h1' : (inner ℝ (Φ zR) uE / ‖uE‖ ^ 2 - (kk i : ℝ)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) hk 2
            exact mul_le_mul_of_nonneg_right h1' (sq_nonneg _)
          nlinarith [hhalf]
        calc ‖Φ (fun k => (X i k : ℝ))‖ = Real.sqrt (‖Φ (fun k => (X i k : ℝ))‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖Ψ (fun k => (e' i k : ℝ))‖ ^ 2 + (‖uE‖ / 2) ^ 2) := Real.sqrt_le_sqrt hsq
          _ ≤ ‖Ψ (fun k => (e' i k : ℝ))‖ + ‖uE‖ / 2 := sqrt_sq_add_sq_le (norm_nonneg _) (by positivity)
      have hXbij : Function.Bijective
          (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • X i) := by
        have hsum : ∀ c : ℤ × (Fin n → ℤ),
            (∑ j : Fin n, (∑ i : Fin n, c.2 i * (e' i j)) • v j)
              = ∑ i : Fin n, c.2 i • (∑ j : Fin n, (e' i j) • v j) := by
          intro c
          have h1 : ∀ j : Fin n, (∑ i : Fin n, c.2 i * (e' i j)) • v j
              = ∑ i : Fin n, c.2 i • ((e' i j) • v j) := by
            intro j
            rw [Finset.sum_smul]
            exact Finset.sum_congr rfl (fun i _ => (smul_smul _ _ _).symm)
          rw [show (∑ j : Fin n, (∑ i : Fin n, c.2 i * (e' i j)) • v j)
              = ∑ j : Fin n, ∑ i : Fin n, c.2 i • ((e' i j) • v j) from
            Finset.sum_congr rfl (fun j _ => h1 j)]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun i _ => by rw [← Finset.smul_sum])
        have hshear : Function.Bijective (fun c : ℤ × (Fin n → ℤ) =>
            (c.1 - ∑ i, c.2 i * kk i, fun j => ∑ i, c.2 i * (e' i j))) := by
          constructor
          · rintro ⟨a, c⟩ ⟨a', c'⟩ h
            have h2 : (fun j => ∑ i, c i * (e' i j)) = (fun j => ∑ i, c' i * (e' i j)) := by
              simpa using congrArg Prod.snd h
            have hc : c = c' := by
              have hzero : ∑ i, (c - c') i • e' i = 0 := by
                rw [show (fun i => (c - c') i • e' i) = (fun i => c i • e' i - c' i • e' i) from by
                  funext i; rw [Pi.sub_apply, sub_smul]]
                rw [Finset.sum_sub_distrib]
                have heq : ∑ i, c i • e' i = ∑ i, c' i • e' i := by
                  ext j
                  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun h2 j
                rw [heq, sub_self]
              funext i
              have hci := (Fintype.linearIndependent_iff.mp e'.linearIndependent) (c - c') hzero i
              have : c i - c' i = 0 := hci
              exact sub_eq_zero.mp this
            have h3 : a - ∑ i, c i * kk i = a' - ∑ i, c' i * kk i := by
              simpa using congrArg Prod.fst h
            rw [hc] at h3
            exact Prod.ext (by omega) hc
          · rintro ⟨b, d⟩
            have hrepr : ∑ i, (e'.repr d) i • e' i = d := Module.Basis.sum_repr e' d
            refine ⟨(b + ∑ i, (e'.repr d) i * kk i, fun i => (e'.repr d) i), ?_⟩
            show (b + ∑ i, (e'.repr d) i * kk i - ∑ i, (e'.repr d) i * kk i,
                fun j => ∑ i, (e'.repr d) i * (e' i j)) = (b, d)
            rw [Prod.mk.injEq]
            constructor
            · ring
            · ext j
              have := congrFun (congrArg (fun z : Fin n → ℤ => fun j => z j) hrepr) j
              simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
        have hTeq : (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • v i)
            ∘ (fun c : ℤ × (Fin n → ℤ) =>
                (c.1 - ∑ i, c.2 i * kk i, fun j => ∑ i, c.2 i * (e' i j)))
            = (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • X i) := by
          funext c
          simp only [Function.comp_apply]
          rw [hX]
          simp only [Pi.sub_apply]
          rw [hsum c]
          have hrw : ∀ i : Fin n, c.2 i • ((∑ j, (e' i j) • v j) - kk i • u)
              = c.2 i • (∑ j, (e' i j) • v j) - (c.2 i * kk i) • u := by
            intro i; rw [smul_sub, smul_smul]
          simp only [hrw]
          rw [Finset.sum_sub_distrib]
          have hAsum : (∑ i : Fin n, (c.2 i * kk i) • u) = (∑ i : Fin n, c.2 i * kk i) • u := by
            rw [← Finset.sum_smul]
          rw [hAsum, sub_smul]
          abel
        rw [← hTeq]
        exact hvBij.comp hshear
      have hconsli : LinearIndependent ℤ (Fin.cons u X) := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hc' : (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • X i)
            (c 0, fun i => c i.succ)
            = (fun c : ℤ × (Fin n → ℤ) => c.1 • u + ∑ i, c.2 i • X i) (0, 0) := by
          have h := hc
          rw [Fin.sum_univ_succ] at h
          simpa using h
        have hinj := hXbij.1 hc'
        have h0 : c 0 = 0 := congrArg Prod.fst hinj
        have hsucc : (fun i : Fin n => c i.succ) = 0 := congrArg Prod.snd hinj
        intro i
        obtain ⟨m, hm⟩ := i
        rcases m with _ | m
        · have hi : (⟨0, hm⟩ : Fin (n + 1)) = 0 := rfl
          rw [hi]; exact h0
        · have hi : (⟨m + 1, hm⟩ : Fin (n + 1)) = (⟨m, by omega⟩ : Fin n).succ := rfl
          rw [hi]; exact congrFun hsucc ⟨m, by omega⟩
      have hconsspan : Submodule.span ℤ (Set.range (Fin.cons u X)) = ⊤ := by
        rw [Submodule.eq_top_iff']
        intro x
        obtain ⟨c, hc⟩ := hXbij.2 x
        rw [← hc]
        refine Submodule.add_mem _
          (Submodule.smul_mem _ c.1 (Submodule.subset_span (Set.mem_range_self 0))) ?_
        refine Submodule.sum_mem _ fun i _ => ?_
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i.succ))
      refine ⟨Module.Basis.mk hconsli (le_of_eq hconsspan.symm), ?_⟩
      have hnormu : ‖uE‖ = latMin Φ 1 := by rw [huE]; exact hu1
      have hnormu_le : ‖uE‖ ≤ latMin Φ (n + 1) := by
        rw [hnormu]; exact latMin_mono Φ (by omega) (le_refl _)
      rw [Fin.sum_univ_succ]
      simp only [Module.Basis.coe_mk, Fin.cons_zero, Fin.cons_succ]
      calc ‖Φ (fun k => (u k : ℝ))‖ + ∑ i : Fin n, ‖Φ (fun k => (X i k : ℝ))‖
          = ‖uE‖ + ∑ i : Fin n, ‖Φ (fun k => (X i k : ℝ))‖ := by rw [← huE]
        _ ≤ ‖uE‖ + ∑ i : Fin n, (‖Ψ (fun k => (e' i k : ℝ))‖ + ‖uE‖ / 2) := by
            gcongr with i
            exact hXbound i
        _ = ‖uE‖ + (∑ i : Fin n, ‖Ψ (fun k => (e' i k : ℝ))‖) + n * (‖uE‖ / 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin]; ring
        _ ≤ latMin Φ (n + 1) + C' * latMin Φ (n + 1) + n * (latMin Φ (n + 1) / 2) := by
            have h2 : ∑ i : Fin n, ‖Ψ (fun k => (e' i k : ℝ))‖ ≤ C' * latMin Φ (n + 1) :=
              he'.trans (mul_le_mul_of_nonneg_left hΨlat hC'pos.le)
            have h3 : (n : ℝ) * (‖uE‖ / 2) ≤ n * (latMin Φ (n + 1) / 2) := by
              gcongr
            linarith
        _ = (1 + C' + (n : ℝ) / 2) * latMin Φ (n + 1) := by ring

/-- **A rank-`R` lattice has a basis of vectors bounded by a constant times its `R`-th successive
minimum.** -/
theorem exists_short_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (R : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : LatMap (ι := ι) R), Function.Injective Φ →
      ∃ e : Module.Basis (Fin R) ℤ (Fin R → ℤ),
        ∑ i, ‖Φ (fun k => ((e i) k : ℝ))‖ ≤ C * latMin Φ R :=
  exists_short_basis_aux R

end Work.HP
