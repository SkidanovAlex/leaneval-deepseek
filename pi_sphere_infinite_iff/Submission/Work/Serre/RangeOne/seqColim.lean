import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup

/-!
# The sequential colimit of a chain of closed embeddings

Given a chain of closed embeddings `X 0 → X 1 → ⋯`, we construct its colimit `Z` as the quotient of
`Σ s, X s` by the relation "equal in some higher level", topologised so that a set is open iff all
its preimages under the structure maps `ι s : X s → Z` are open.  The facts used downstream are

* `SeqChain.exists_factor`: every map from a compact space into `Z` factors through one of the
  `X s`;
* `SeqChain.compressRel`: if the pair `(X T, range (upAt S T))` compresses in dimension `d` for all
  `T ≥ S`, then the pair `(Z, range (ι S))` compresses in dimension `d`.
-/

open scoped Topology

namespace Work.Serre.RangeOne

/-- A chain `X 0 → X 1 → ⋯` of closed embeddings. -/
structure SeqChain where
  X : ℕ → Type
  top : ∀ s, TopologicalSpace (X s)
  step : ∀ s, ContinuousMap (X s) (X (s + 1))
  closed : ∀ s, Topology.IsClosedEmbedding (step s)

attribute [instance] SeqChain.top

namespace SeqChain

variable (C : SeqChain)

/-- The map climbing from level `s` to level `n ≥ s` by iterating the steps. -/
noncomputable def upAt (s n : ℕ) (h : s ≤ n) : C.X s → C.X n :=
  if hsn : s = n then fun x => cast (congrArg C.X hsn) x
  else fun x => upAt (s + 1) n (by omega) (C.step s x)
termination_by n - s
decreasing_by omega

theorem upAt_proof_irrel {s n : ℕ} (h₁ h₂ : s ≤ n) (x : C.X s) :
    C.upAt s n h₁ x = C.upAt s n h₂ x := by
  rw [Subsingleton.elim h₁ h₂]

theorem upAt_self {s : ℕ} (h : s ≤ s) (x : C.X s) : C.upAt s s h x = x := by
  rw [upAt]
  split_ifs with hh
  · exact (congrArg (fun p => cast (congrArg C.X p) x) (Subsingleton.elim hh rfl)).trans rfl
  · exact absurd rfl hh

theorem upAt_step {s n : ℕ} (h : s ≤ n) (h' : s + 1 ≤ n) (hsn : s ≠ n) (x : C.X s) :
    C.upAt s n h x = C.upAt (s + 1) n h' (C.step s x) := by
  rw [upAt]
  split_ifs with hh
  · exact absurd hh hsn
  · exact C.upAt_proof_irrel _ h' _

theorem upAt_comp_aux (d : ℕ) : ∀ (s n m : ℕ) (hsm : s ≤ m) (hsn : s ≤ n) (hnm : n ≤ m),
    n - s = d → ∀ x : C.X s, C.upAt n m hnm (C.upAt s n hsn x) = C.upAt s m hsm x := by
  induction d with
  | zero =>
      intro s n m hsm hsn hnm hd x
      have hsn' : s = n := by omega
      subst hsn'
      exact (congrArg (fun y => C.upAt s m hnm y) (C.upAt_self hsn x)).trans
        (C.upAt_proof_irrel hnm hsm x)
  | succ d ih =>
      intro s n m hsm hsn hnm hd x
      have h1 : s + 1 ≤ n := by omega
      have h2 : s + 1 ≤ m := by omega
      have hne : s ≠ n := by omega
      have hne' : s ≠ m := by omega
      rw [C.upAt_step hsn h1 hne x, C.upAt_step hsm h2 hne' x]
      exact ih (s + 1) n m h2 h1 hnm (by omega) (C.step s x)

/-- **Coherence of the climbing maps**: climbing from `s` to `m` is the same as climbing to `n`
first and then to `m`. -/
theorem upAt_comp {s n m : ℕ} (hsm : s ≤ m) (hsn : s ≤ n) (hnm : n ≤ m) (x : C.X s) :
    C.upAt n m hnm (C.upAt s n hsn x) = C.upAt s m hsm x :=
  C.upAt_comp_aux (n - s) s n m hsm hsn hnm rfl x

theorem upAt_injective_aux (d : ℕ) : ∀ (s n : ℕ) (h : s ≤ n), n - s = d →
    Function.Injective (C.upAt s n h) := by
  induction d with
  | zero =>
      intro s n h hd
      have hsn : s = n := by omega
      subst hsn
      intro x y hxy
      rw [C.upAt_self h x, C.upAt_self h y] at hxy
      exact hxy
  | succ d ih =>
      intro s n h hd
      have h' : s + 1 ≤ n := by omega
      have hne : s ≠ n := by omega
      intro x y hxy
      rw [C.upAt_step h h' hne x, C.upAt_step h h' hne y] at hxy
      exact (C.closed s).isEmbedding.injective (ih (s + 1) n h' (by omega) hxy)

theorem upAt_injective {s n : ℕ} (h : s ≤ n) : Function.Injective (C.upAt s n h) :=
  C.upAt_injective_aux (n - s) s n h rfl

theorem upAt_continuous_aux (d : ℕ) : ∀ (s n : ℕ) (h : s ≤ n), n - s = d →
    Continuous (C.upAt s n h) := by
  induction d with
  | zero =>
      intro s n h hd
      have hsn : s = n := by omega
      subst hsn
      rw [funext (C.upAt_self h)]
      exact continuous_id
  | succ d ih =>
      intro s n h hd
      have h' : s + 1 ≤ n := by omega
      have hne : s ≠ n := by omega
      have hfun : C.upAt s n h = (C.upAt (s + 1) n h') ∘ (C.step s) := by
        funext x
        exact C.upAt_step h h' hne x
      rw [hfun]
      exact (ih (s + 1) n h' (by omega)).comp (C.step s).continuous

theorem upAt_isClosedEmbedding_aux (d : ℕ) : ∀ (s n : ℕ) (h : s ≤ n), n - s = d →
    Topology.IsClosedEmbedding (C.upAt s n h) := by
  induction d with
  | zero =>
      intro s n h hd
      have hsn : s = n := by omega
      subst hsn
      rw [funext (C.upAt_self h)]
      exact Topology.IsClosedEmbedding.id
  | succ d ih =>
      intro s n h hd
      have h' : s + 1 ≤ n := by omega
      have hne : s ≠ n := by omega
      have hfun : C.upAt s n h = (C.upAt (s + 1) n h') ∘ (C.step s) := by
        funext x
        exact C.upAt_step h h' hne x
      rw [hfun]
      exact (ih (s + 1) n h' (by omega)).comp (C.closed s)

theorem upAt_isClosedEmbedding {s n : ℕ} (h : s ≤ n) :
    Topology.IsClosedEmbedding (C.upAt s n h) :=
  C.upAt_isClosedEmbedding_aux (n - s) s n h rfl

/-! ## The colimit -/

/-- The relation "the two points of `Σ s, X s` agree at some common higher level". -/
def rel (a b : Σ s, C.X s) : Prop :=
  ∃ n : ℕ, ∃ h₁ : a.1 ≤ n, ∃ h₂ : b.1 ≤ n, C.upAt a.1 n h₁ a.2 = C.upAt b.1 n h₂ b.2

theorem rel_refl (a : Σ s, C.X s) : C.rel a a :=
  ⟨a.1, le_rfl, le_rfl, rfl⟩

theorem rel_symm {a b : Σ s, C.X s} (h : C.rel a b) : C.rel b a := by
  obtain ⟨n, h₁, h₂, e⟩ := h
  exact ⟨n, h₂, h₁, e.symm⟩

theorem rel_trans {a b c : Σ s, C.X s} (hab : C.rel a b) (hbc : C.rel b c) : C.rel a c := by
  obtain ⟨n, h₁, h₂, e₁⟩ := hab
  obtain ⟨m, h₃, h₄, e₂⟩ := hbc
  refine ⟨max n m, le_trans h₁ (le_max_left n m), le_trans h₄ (le_max_right n m), ?_⟩
  have hb : b.1 ≤ max n m := le_trans h₂ (le_max_left n m)
  calc C.upAt a.1 (max n m) (le_trans h₁ (le_max_left n m)) a.2
      = C.upAt n (max n m) (le_max_left n m) (C.upAt a.1 n h₁ a.2) :=
        (C.upAt_comp (le_trans h₁ (le_max_left n m)) h₁ (le_max_left n m) a.2).symm
    _ = C.upAt n (max n m) (le_max_left n m) (C.upAt b.1 n h₂ b.2) := by rw [e₁]
    _ = C.upAt b.1 (max n m) hb b.2 := C.upAt_comp hb h₂ (le_max_left n m) b.2
    _ = C.upAt m (max n m) (le_max_right n m) (C.upAt b.1 m h₃ b.2) :=
        (C.upAt_comp hb h₃ (le_max_right n m) b.2).symm
    _ = C.upAt m (max n m) (le_max_right n m) (C.upAt c.1 m h₄ c.2) := by rw [e₂]
    _ = C.upAt c.1 (max n m) (le_trans h₄ (le_max_right n m)) c.2 :=
        C.upAt_comp (le_trans h₄ (le_max_right n m)) h₄ (le_max_right n m) c.2

/-- The setoid whose quotient is the colimit. -/
def setoid : Setoid (Σ s, C.X s) where
  r := C.rel
  iseqv := ⟨C.rel_refl, fun h => C.rel_symm h, fun h₁ h₂ => C.rel_trans h₁ h₂⟩

/-- The colimit of the chain. -/
def Z : Type := Quotient C.setoid

/-- The structure map from level `s`. -/
def iota (s : ℕ) (x : C.X s) : C.Z := Quotient.mk C.setoid ⟨s, x⟩

theorem iota_eq_iff {s t : ℕ} (x : C.X s) (y : C.X t) :
    C.iota s x = C.iota t y ↔ ∃ n h₁ h₂, C.upAt s n h₁ x = C.upAt t n h₂ y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem iota_step (s : ℕ) (x : C.X s) : C.iota (s + 1) (C.step s x) = C.iota s x := by
  refine (C.iota_eq_iff (C.step s x) x).mpr ⟨s + 1, le_rfl, Nat.le_succ s, ?_⟩
  rw [C.upAt_self le_rfl, C.upAt_step (Nat.le_succ s) le_rfl (by omega) x, C.upAt_self le_rfl]

theorem iota_injective (s : ℕ) : Function.Injective (C.iota s) := by
  intro x y hxy
  obtain ⟨n, h₁, h₂, e⟩ := (C.iota_eq_iff x y).mp hxy
  have e' : C.upAt s n h₁ x = C.upAt s n h₁ y := by
    rw [e, C.upAt_proof_irrel h₂ h₁ y]
  exact C.upAt_injective h₁ e'

/-- The structure maps are compatible with the climbing maps. -/
theorem iota_compat {s t : ℕ} (h : s ≤ t) (x : C.X s) :
    C.iota s x = C.iota t (C.upAt s t h x) :=
  (C.iota_eq_iff x (C.upAt s t h x)).mpr ⟨t, h, le_rfl, by rw [C.upAt_self le_rfl]⟩

/-! ## The topology -/

instance instTopologicalSpace : TopologicalSpace C.Z :=
  ⨆ s, TopologicalSpace.coinduced (C.iota s) (C.top s)

theorem isOpen_iff {U : Set C.Z} : IsOpen U ↔ ∀ s, IsOpen ((C.iota s) ⁻¹' U) := by
  rw [isOpen_iSup_iff]
  exact forall_congr' fun s => isOpen_coinduced

theorem isClosed_iff {S : Set C.Z} : IsClosed S ↔ ∀ s, IsClosed ((C.iota s) ⁻¹' S) := by
  rw [isOpen_compl_iff.symm, isOpen_iSup_iff]
  exact forall_congr' fun s => by
    rw [isOpen_coinduced, Set.preimage_compl, isOpen_compl_iff]

theorem continuous_iota (s : ℕ) : Continuous (C.iota s) :=
  ⟨fun U hU => (C.isOpen_iff.mp hU) s⟩

theorem isClosed_range_iota (s : ℕ) : IsClosed (Set.range (C.iota s)) := by
  rw [C.isClosed_iff]
  intro t
  rcases lt_or_ge t s with hlt | hle
  · have hts : t ≤ s := le_of_lt hlt
    have h1 : (C.iota t) ⁻¹' (Set.range (C.iota s)) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ?_
      exact ⟨C.upAt t s hts y, (C.iota_compat hts y).symm⟩
    rw [h1]
    exact isClosed_univ
  · have h1 : (C.iota t) ⁻¹' (Set.range (C.iota s)) = Set.range (C.upAt s t hle) := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := hy
        obtain ⟨n, h₁, h₂, e⟩ := (C.iota_eq_iff y x).mp hx.symm
        have hco : C.upAt s n h₂ x = C.upAt t n h₁ (C.upAt s t hle x) := by
          rw [C.upAt_proof_irrel h₂ (le_trans hle h₁) x]
          exact (C.upAt_comp (le_trans hle h₁) hle h₁ x).symm
        have e' : C.upAt t n h₁ y = C.upAt t n h₁ (C.upAt s t hle x) := by
          rw [e, hco]
        exact ⟨x, (C.upAt_injective h₁ e').symm⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, C.iota_compat hle x⟩
    rw [h1]
    exact (C.upAt_isClosedEmbedding hle).isClosed_range

theorem isClosedMap_iota (s : ℕ) : IsClosedMap (C.iota s) := by
  intro Cset hC
  rw [C.isClosed_iff]
  intro t
  rcases lt_or_ge t s with hlt | hle
  · have hts : t ≤ s := le_of_lt hlt
    have h1 : (C.iota t) ⁻¹' (C.iota s '' Cset) = C.upAt t s hts ⁻¹' Cset := by
      ext y
      constructor
      · rintro ⟨c, hc, hcy⟩
        have hyc : C.upAt t s hts y = c :=
          C.iota_injective s ((C.iota_compat hts y).symm.trans hcy.symm)
        rw [Set.mem_preimage, hyc]
        exact hc
      · intro hy
        exact ⟨C.upAt t s hts y, hy, (C.iota_compat hts y).symm⟩
    rw [h1]
    exact hC.preimage (C.upAt_isClosedEmbedding hts).continuous
  · have h1 : (C.iota t) ⁻¹' (C.iota s '' Cset) = C.upAt s t hle '' Cset := by
      ext y
      constructor
      · rintro ⟨c, hc, hcy⟩
        obtain ⟨n, h₁, h₂, e⟩ := (C.iota_eq_iff y c).mp hcy.symm
        have hco : C.upAt s n h₂ c = C.upAt t n h₁ (C.upAt s t hle c) := by
          rw [C.upAt_proof_irrel h₂ (le_trans hle h₁) c]
          exact (C.upAt_comp (le_trans hle h₁) hle h₁ c).symm
        have e' : C.upAt t n h₁ y = C.upAt t n h₁ (C.upAt s t hle c) := by
          rw [e, hco]
        exact ⟨c, hc, C.upAt_injective h₁ e'.symm⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, hc, C.iota_compat hle c⟩
    rw [h1]
    exact (C.upAt_isClosedEmbedding hle).isClosedMap Cset hC

/-- **The structure maps are closed embeddings.** -/
theorem isClosedEmbedding_iota (s : ℕ) : Topology.IsClosedEmbedding (C.iota s) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (C.continuous_iota s) (C.iota_injective s) (C.isClosedMap_iota s)

theorem isEmbedding_iota (s : ℕ) : Topology.IsEmbedding (C.iota s) :=
  (C.isClosedEmbedding_iota s).isEmbedding

/-- **The preimage of the range of a lower structure map**: for `s ≤ t`, a point of `X t` lies in the
image of `X s` exactly when it lies in the range of the climbing map `upAt s t`. -/
theorem preimage_range_iota {s t : ℕ} (h : s ≤ t) :
    (C.iota t) ⁻¹' (Set.range (C.iota s)) = Set.range (C.upAt s t h) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := hy
    obtain ⟨n, h₁, h₂, e⟩ := (C.iota_eq_iff y x).mp hx.symm
    have hco : C.upAt s n h₂ x = C.upAt t n h₁ (C.upAt s t h x) := by
      rw [C.upAt_proof_irrel h₂ (le_trans h h₁) x]
      exact (C.upAt_comp (le_trans h h₁) h h₁ x).symm
    have e' : C.upAt t n h₁ y = C.upAt t n h₁ (C.upAt s t h x) := by rw [e, hco]
    exact ⟨x, (C.upAt_injective h₁ e').symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, C.iota_compat h x⟩

/-- The ranges of the structure maps are increasing. -/
theorem range_iota_subset {s t : ℕ} (h : s ≤ t) :
    Set.range (C.iota s) ⊆ Set.range (C.iota t) :=
  fun _ ⟨y, hy⟩ => ⟨C.upAt s t h y, by rw [← hy, C.iota_compat h y]⟩

end SeqChain

end Work.Serre.RangeOne
