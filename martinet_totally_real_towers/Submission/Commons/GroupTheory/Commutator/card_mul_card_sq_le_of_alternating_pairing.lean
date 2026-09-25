import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Order.Hom.Esakia
import Submission.Commons.LinearAlgebra.Alternating.card_le_of_simple_invariant_alternating_span

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.Commutator

open Additive

theorem zmod_smul_eq_nsmul_val {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    [Module (ZMod n) M] (c : ZMod n) (m : M) : c • m = c.val • m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul]

def AddEquiv.toZModLinearEquiv {n : ℕ} [NeZero n] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module (ZMod n) M] [Module (ZMod n) N] (e : M ≃+ N) : M ≃ₗ[ZMod n] N where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := fun c x => by
    show e (c • x) = c • e x
    rw [zmod_smul_eq_nsmul_val c x, map_nsmul, ← zmod_smul_eq_nsmul_val c (e x)]

theorem span_eq_toZModSubmodule_closure {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M]
    [Module (ZMod n) M] (T : Set M) :
    Submodule.span (ZMod n) T = AddSubgroup.toZModSubmodule n (AddSubgroup.closure T) := by
  have hle1 : Submodule.span (ZMod n) T ≤ AddSubgroup.toZModSubmodule n (AddSubgroup.closure T) :=
    Submodule.span_le.mpr (fun x hx => AddSubgroup.subset_closure hx)
  have h1 : (Submodule.span (ZMod n) T).toAddSubgroup ≤ AddSubgroup.closure T := by
    have h3 := (AddSubgroup.toZModSubmodule n).symm.monotone hle1
    simpa only [AddSubgroup.toZModSubmodule_symm, Submodule.toAddSubgroup_toZModSubmodule,
      OrderIso.symm_apply_apply] using h3
  have h2 : AddSubgroup.closure T ≤ (Submodule.span (ZMod n) T).toAddSubgroup :=
    (AddSubgroup.closure_le _).mpr (fun x hx => Submodule.subset_span hx)
  have h : (Submodule.span (ZMod n) T).toAddSubgroup = AddSubgroup.closure T := le_antisymm h1 h2
  rw [← h, Submodule.toAddSubgroup_toZModSubmodule]

/-- **Abstract bound in multiplicative form.**  Let `p` be a prime, `Q` a finite abelian group
of exponent `p` on which `G` acts irreducibly (via `σ`), and `A` a finite abelian group of
exponent `p` with a `G`-invariant biadditive alternating pairing `b : Q → Q → A` whose image
generates `A` and whose radical is trivial.  Then `|A|² ≤ |Q|`.

Convert to the additive picture (`Additive Q`, `Additive A` are `𝔽_p`-vector spaces because the
groups are abelian of exponent `p`) and apply `Commons.LinearAlgebra.Alternating.
card_le_of_simple_invariant_alternating_span`. -/
theorem card_mul_card_sq_le_of_alternating_pairing {p : ℕ} [Fact p.Prime] {G Q A : Type*}
    [Group G] [CommGroup Q] [Finite Q] [CommGroup A] [Finite A]
    (hpQ : ∀ x : Q, x ^ p = 1) (hpA : ∀ a : A, a ^ p = 1)
    (σ : G →* MulAut Q) (b : Q → Q → A)
    (b_one_left : ∀ a : Q, b 1 a = 1)
    (b_one_right : ∀ a : Q, b a 1 = 1)
    (b_mul_left : ∀ a a' c : Q, b (a * a') c = b a c * b a' c)
    (b_mul_right : ∀ a c c' : Q, b a (c * c') = b a c * b a c')
    (b_self : ∀ a : Q, b a a = 1)
    (b_inv : ∀ (g : G) (a c : Q), b (σ g a) (σ g c) = b a c)
    (b_gen : ∀ y : A, y ∈ Subgroup.closure (Set.range (fun x : Q × Q => b x.1 x.2)))
    (b_rad : ∀ a : Q, (∀ c : Q, b a c = 1) → a = 1)
    (b_simple : ∀ K : Subgroup Q, (∀ (g : G) (a : Q), a ∈ K → σ g a ∈ K) →
      K = ⊥ ∨ K = ⊤) :
    Nat.card A ^ 2 ≤ Nat.card Q := by
  haveI hpne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI hV : Module (ZMod p) (Additive Q) :=
    AddCommGroup.zmodModule (fun x => toMul_eq_one.mp (by rw [toMul_nsmul]; exact hpQ x.toMul))
  haveI hW : Module (ZMod p) (Additive A) :=
    AddCommGroup.zmodModule (fun x => toMul_eq_one.mp (by rw [toMul_nsmul]; exact hpA x.toMul))
  -- biadditive map
  have hF1 : ∀ m1 m2 n : Additive Q,
      (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) (m1 + m2) n
      = (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m1 n
        + (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m2 n := by
    intro m1 m2 n
    simp only [toMul_add, b_mul_left, ofMul_mul]
  have hF3 : ∀ m n1 n2 : Additive Q,
      (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m (n1 + n2)
      = (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n1
        + (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n2 := by
    intro m n1 n2
    simp only [toMul_add, b_mul_right, ofMul_mul]
  have hF2nat : ∀ (k : ℕ) (m n : Additive Q),
      (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) (k • m) n
      = k • (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n := by
    intro k
    induction k with
    | zero =>
        intro m n
        simp only [zero_nsmul, toMul_zero, b_one_left, ofMul_one]
    | succ k ih =>
        intro m n
        rw [succ_nsmul, succ_nsmul]
        rw [show (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) (k • m + m) n
              = (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) (k • m) n
                + (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n from by
              simp only [toMul_add, b_mul_left, ofMul_mul]]
        rw [ih]
  have hF4nat : ∀ (k : ℕ) (m n : Additive Q),
      (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m (k • n)
      = k • (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n := by
    intro k
    induction k with
    | zero =>
        intro m n
        simp only [zero_nsmul, toMul_zero, b_one_right, ofMul_one]
    | succ k ih =>
        intro m n
        rw [succ_nsmul, succ_nsmul]
        rw [show (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m (k • n + n)
              = (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m (k • n)
                + (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n from by
              simp only [toMul_add, b_mul_right, ofMul_mul]]
        rw [ih]
  have hF2 : ∀ (c : ZMod p) (m n : Additive Q),
      (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) (c • m) n
      = c • (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n := by
    intro c m n
    rw [zmod_smul_eq_nsmul_val c m, zmod_smul_eq_nsmul_val c _]
    exact hF2nat c.val m n
  have hF4 : ∀ (c : ZMod p) (m n : Additive Q),
      (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m (c • n)
      = c • (fun x y : Additive Q => Additive.ofMul (b x.toMul y.toMul)) m n := by
    intro c m n
    rw [zmod_smul_eq_nsmul_val c n, zmod_smul_eq_nsmul_val c _]
    exact hF4nat c.val m n
  let β := LinearMap.mk₂ (R := ZMod p) (M := Additive Q) (Nₗ := Additive Q) (Pₗ := Additive A)
      (fun x y => Additive.ofMul (b x.toMul y.toMul)) hF1 hF2 hF3 hF4
  -- the action ρ
  let ρ : G →* Additive Q ≃ₗ[ZMod p] Additive Q :=
    { toFun := fun g => AddEquiv.toZModLinearEquiv
        { toFun := fun x => Additive.ofMul (σ g x.toMul)
          invFun := fun x => Additive.ofMul ((σ g).symm x.toMul)
          left_inv := by
            intro x
            simp
          right_inv := by
            intro x
            simp
          map_add' := by
            intro x y
            simp only [toMul_add, map_mul, ofMul_mul] }
      map_one' := by
        ext x
        show Additive.ofMul (σ 1 x.toMul) = x
        rw [map_one σ]
        simp
      map_mul' := by
        intro g h
        ext x
        show Additive.ofMul (σ (g * h) x.toMul)
          = Additive.ofMul (σ g ((Additive.ofMul (σ h x.toMul)).toMul))
        rw [map_mul σ]
        simp }
  have hρ_apply : ∀ (g : G) (x : Additive Q), ρ g x = Additive.ofMul (σ g x.toMul) := by
    intro g x
    rfl
  have halt : ∀ v : Additive Q, β v v = 0 := by
    intro v
    show Additive.ofMul (b v.toMul v.toMul) = 0
    rw [b_self, ofMul_one]
  have hinv : ∀ (g : G) (v w : Additive Q), β (ρ g v) (ρ g w) = β v w := by
    intro g v w
    show Additive.ofMul (b (ρ g v).toMul (ρ g w).toMul)
      = Additive.ofMul (b v.toMul w.toMul)
    rw [hρ_apply, hρ_apply, toMul_ofMul, toMul_ofMul, b_inv]
  have hrad : ∀ v : Additive Q, (∀ w : Additive Q, β v w = 0) → v = 0 := by
    intro v hv
    apply toMul_eq_one.mp
    apply b_rad v.toMul
    intro c
    have h := hv (Additive.ofMul c)
    have h' : Additive.ofMul (b v.toMul c) = 0 := h
    exact ofMul_eq_zero.mp h'
  have hspan : Submodule.span (ZMod p) (Set.range (fun x : Additive Q × Additive Q => β x.1 x.2))
      = ⊤ := by
    set S : Set A := Set.range (fun x : Q × Q => b x.1 x.2) with hS
    have hgen : Subgroup.closure S = ⊤ := eq_top_iff.mpr (fun y _ => b_gen y)
    have hcl : AddSubgroup.closure (Additive.ofMul '' S) = ⊤ := by
      have h1 := Subgroup.toAddSubgroup_closure (G := A) S
      rw [hgen] at h1
      have h1' : (⊤ : AddSubgroup (Additive A)) = AddSubgroup.closure (Additive.toMul ⁻¹' S) := h1
      have hset : (Additive.toMul ⁻¹' S : Set (Additive A)) = Additive.ofMul '' S := by
        ext x
        constructor
        · intro hx
          exact ⟨x.toMul, hx, by simp⟩
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
      rw [hset] at h1'
      rw [h1']
    have himg : Set.range (fun x : Additive Q × Additive Q => β x.1 x.2)
        = Additive.ofMul '' S := by
      ext y
      constructor
      · rintro ⟨⟨v, w⟩, rfl⟩
        exact ⟨b v.toMul w.toMul, ⟨(v.toMul, w.toMul), rfl⟩, rfl⟩
      · rintro ⟨y, ⟨⟨a, c⟩, rfl⟩, rfl⟩
        exact ⟨(Additive.ofMul a, Additive.ofMul c), rfl⟩
    rw [himg, span_eq_toZModSubmodule_closure, hcl]
    exact OrderIso.map_top _
  have hsimple : ∀ W : Submodule (ZMod p) (Additive Q),
      (∀ (g : G) (v : Additive Q), v ∈ W → ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    set K : Subgroup Q := AddSubgroup.toSubgroup' W.toAddSubgroup with hK
    have hKm : ∀ (g : G) (a : Q), a ∈ K → σ g a ∈ K := by
      intro g a ha
      rw [AddSubgroup.mem_toSubgroup'] at ha ⊢
      have h1 : ρ g (Additive.ofMul a) = Additive.ofMul (σ g a) := by
        rw [hρ_apply]
        rfl
      rw [← h1]
      exact hW g _ ha
    rcases b_simple K hKm with hbot | htop
    · left
      have hW' : W.toAddSubgroup = ⊥ := by
        have h := congrArg (Subgroup.toAddSubgroup (G := Q)) hbot
        simpa [hK] using h
      calc W = AddSubgroup.toZModSubmodule p W.toAddSubgroup :=
            (Submodule.toAddSubgroup_toZModSubmodule p W).symm
        _ = AddSubgroup.toZModSubmodule p (⊥ : AddSubgroup (Additive Q)) := by rw [hW']
        _ = ⊥ := OrderIso.map_bot _
    · right
      have hW' : W.toAddSubgroup = ⊤ := by
        have h := congrArg (Subgroup.toAddSubgroup (G := Q)) htop
        simpa [hK] using h
      calc W = AddSubgroup.toZModSubmodule p W.toAddSubgroup :=
            (Submodule.toAddSubgroup_toZModSubmodule p W).symm
        _ = AddSubgroup.toZModSubmodule p (⊤ : AddSubgroup (Additive Q)) := by rw [hW']
        _ = ⊤ := OrderIso.map_top _
  have h := Commons.LinearAlgebra.Alternating.card_le_of_simple_invariant_alternating_span
      (p := p) ρ β halt hinv hspan hrad hsimple
  rwa [Nat.card_congr Additive.ofMul, Nat.card_congr Additive.ofMul] at h

end Commons.GroupTheory.Commutator