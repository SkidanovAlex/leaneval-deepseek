import Mathlib
import Submission.Work.Smooth.JordanSeparation.Transfer

namespace Work.Smooth.JordanSeparation

theorem exists_homeomorph_of_compatible_chain
    {r : ℕ → ℝ} (hrpos : ∀ n, 0 < r n) (hrmon : Monotone r) (hrle : ∀ n, r n ≤ 1)
    (hrlim : ∀ x : ℝ, x < 1 → ∃ n, x ≤ r n)
    {K : ℕ → Set ℂ} (hKm : ∀ n, IsCompact (K n))
    (hKnest : ∀ n, K n ⊆ interior (K (n + 1)))
    (h : ∀ n, Metric.ball (0 : ℂ) (r n) ≃ₜ interior (K n))
    (hcompat : ∀ n (x : Metric.ball (0 : ℂ) (r n)),
      (h (n + 1) ⟨(x : ℂ), Metric.mem_ball.mpr
          (lt_of_lt_of_le (Metric.mem_ball.mp x.2) (hrmon (Nat.le_succ n)))⟩ : ℂ) =
        (h n x : ℂ)) :
    Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ (⋃ n, interior (K n))) := by
  classical
  let B : ℕ → Set ℂ := fun n => Metric.ball (0 : ℂ) (r n)
  let D : Set ℂ := Metric.ball (0 : ℂ) 1
  let U : Set ℂ := ⋃ n, interior (K n)
  have hrlt : ∀ w : ℝ, w < 1 → ∃ n, w < r n := by
    intro w hw
    obtain ⟨y, hwy, hy1⟩ := exists_between hw
    obtain ⟨n, hn⟩ := hrlim y hy1
    exact ⟨n, lt_of_lt_of_le hwy hn⟩
  let incl : ∀ {n m : ℕ}, n ≤ m → B n → B m :=
    fun {n m} hnm x => ⟨(x : ℂ), lt_of_lt_of_le x.2 (hrmon hnm)⟩
  have hcompat' : ∀ (n : ℕ) (x : B n),
      (h (n + 1) (incl (Nat.le_succ n) x) : ℂ) = (h n x : ℂ) := by
    intro n x
    have key : (⟨(x : ℂ), Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp x.2) (hrmon (Nat.le_succ n)))⟩ : B (n + 1))
        = incl (Nat.le_succ n) x := Subtype.ext rfl
    rw [← key]
    exact hcompat n x
  have himage : ∀ {n m : ℕ} (hnm : n ≤ m) (x : B n),
      (h m (incl hnm x) : ℂ) = (h n x : ℂ) := by
    intro n m hnm
    refine Nat.le_induction (m := n)
      (P := fun m hm => ∀ x : B n, (h m (incl hm x) : ℂ) = (h n x : ℂ)) ?_ ?_ m hnm
    · intro x
      exact congrArg (fun z : B n => (h n z : ℂ)) (Subtype.ext rfl)
    · intro k hk ih x
      have hstep := hcompat' k (incl hk x)
      calc (h (k + 1) (incl (Nat.le_trans hk (Nat.le_succ k)) x) : ℂ)
          = (h (k + 1) (incl (Nat.le_succ k) (incl hk x)) : ℂ) := by congr 1
        _ = (h k (incl hk x) : ℂ) := hstep
        _ = (h n x : ℂ) := ih x
  -- choice of indices
  let xex : ∀ x : D, ∃ n, dist (x : ℂ) 0 < r n := fun x => hrlt (dist (x : ℂ) 0) x.2
  let N : D → ℕ := fun x => Nat.find (xex x)
  let zex : ∀ z : U, ∃ n, (z : ℂ) ∈ interior (K n) := fun z => Set.mem_iUnion.mp z.2
  let M : U → ℕ := fun z => Nat.find (zex z)
  let F : D → U := fun x => ⟨↑(h (N x) (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x))),
    Set.mem_iUnion.mpr ⟨N x, (h (N x) (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x))).2⟩⟩
  let G : U → D := fun z =>
    ⟨↑((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))),
     lt_of_lt_of_le ((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))).2
       (hrle (M z))⟩
  -- F described on each `B n`
  have hF_eq : ∀ (n : ℕ) (x : D) (hx : dist (x : ℂ) 0 < r n),
      F x = (⟨↑(h n (⟨(x : ℂ), hx⟩ : B n)),
        Set.mem_iUnion.mpr ⟨n, (h n (⟨(x : ℂ), hx⟩ : B n)).2⟩⟩ : U) := by
    intro n x hx
    have hle : N x ≤ n := Nat.find_min' (xex x) hx
    have hkey := himage hle (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x))
    apply Subtype.ext
    show (↑(h (N x) (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x))) : ℂ)
      = (↑(h n (⟨(x : ℂ), hx⟩ : B n)) : ℂ)
    rw [← hkey]
  -- G described on each `interior (K n)`
  have hG_eq : ∀ (n : ℕ) (z : U) (hz : (z : ℂ) ∈ interior (K n)),
      G z = (⟨↑((h n).symm (⟨(z : ℂ), hz⟩ : interior (K n))),
        lt_of_lt_of_le ((h n).symm (⟨(z : ℂ), hz⟩ : interior (K n))).2 (hrle n)⟩ : D) := by
    intro n z hz
    have hle : M z ≤ n := Nat.find_min' (zex z) hz
    have hinj : h n (incl hle ((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))))
        = h n ((h n).symm (⟨(z : ℂ), hz⟩ : interior (K n))) := by
      apply Subtype.ext
      rw [himage hle]
      simp only [Homeomorph.apply_symm_apply]
    have hval : (((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))) : ℂ)
        = (((h n).symm (⟨(z : ℂ), hz⟩ : interior (K n))) : ℂ) :=
      congrArg (fun w : B n => (w : ℂ)) ((h n).injective hinj)
    apply Subtype.ext
    show (((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))) : ℂ)
      = (((h n).symm (⟨(z : ℂ), hz⟩ : interior (K n))) : ℂ)
    exact hval
  -- left inverse
  have hleft : Function.LeftInverse G F := by
    intro x
    have hFxval : (((F x : U) : ℂ)) = ↑(h (N x) (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x))) := rfl
    have hmem : (((F x : U) : ℂ)) ∈ interior (K (N x)) := by
      rw [hFxval]
      exact (h (N x) (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x))).2
    rw [hG_eq (N x) (F x) hmem]
    apply Subtype.ext
    show (((h (N x)).symm (⟨((F x : U) : ℂ), hmem⟩ : interior (K (N x)))) : ℂ) = (x : ℂ)
    have heq : (⟨((F x : U) : ℂ), hmem⟩ : interior (K (N x)))
        = h (N x) (⟨(x : ℂ), Nat.find_spec (xex x)⟩ : B (N x)) := Subtype.ext hFxval
    rw [heq, Homeomorph.symm_apply_apply]
  -- right inverse
  have hright : Function.RightInverse G F := by
    intro z
    have hGzval : (((G z : D) : ℂ))
        = ↑((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))) := rfl
    have hmem : dist (((G z : D)) : ℂ) 0 < r (M z) := by
      rw [hGzval]
      exact ((h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z)))).2
    rw [hF_eq (M z) (G z) hmem]
    apply Subtype.ext
    show (↑(h (M z) (⟨((G z : D) : ℂ), hmem⟩ : B (M z))) : ℂ) = (z : ℂ)
    have heq : (⟨((G z : D) : ℂ), hmem⟩ : B (M z))
        = (h (M z)).symm (⟨(z : ℂ), Nat.find_spec (zex z)⟩ : interior (K (M z))) :=
      Subtype.ext hGzval
    rw [heq, Homeomorph.apply_symm_apply]
  -- openness of the index sets and their cover
  let S : ℕ → Set D := fun n => {y | (y : ℂ) ∈ B n}
  have hSopen : ∀ n, IsOpen (S n) := by
    intro n
    exact (Metric.isOpen_ball (x := (0 : ℂ)) (ε := r n)).preimage continuous_subtype_val
  have hScover : (⋃ n, S n) = Set.univ := by
    ext y
    constructor
    · intro _; exact Set.mem_univ y
    · intro _; exact Set.mem_iUnion.mpr (hrlt (dist (y : ℂ) 0) y.2)
  have hFcont : Continuous F := by
    refine continuous_of_continuousOn_iUnion_of_isOpen (s := S) ?_ hSopen hScover
    intro n
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun y : S n => (⟨(y : ℂ), y.2⟩ : B n)) :=
      (continuous_subtype_val.comp continuous_subtype_val :
        Continuous (fun y : S n => (y : ℂ))).subtype_mk (fun y => y.2)
    have hcc : Continuous (fun y : S n => (↑(h n (⟨(y : ℂ), y.2⟩ : B n)) : ℂ)) :=
      ((h n).continuous.comp hc).subtype_val
    have hcont : Continuous (fun y : S n =>
        (⟨↑(h n (⟨(y : ℂ), y.2⟩ : B n)),
          Set.mem_iUnion.mpr ⟨n, (h n (⟨(y : ℂ), y.2⟩ : B n)).2⟩⟩ : U)) :=
      hcc.subtype_mk (fun y => Set.mem_iUnion.mpr ⟨n, (h n (⟨(y : ℂ), y.2⟩ : B n)).2⟩)
    refine hcont.congr (fun y => ?_)
    show (⟨↑(h n (⟨(y : ℂ), y.2⟩ : B n)),
        Set.mem_iUnion.mpr ⟨n, (h n (⟨(y : ℂ), y.2⟩ : B n)).2⟩⟩ : U) = F (y : D)
    exact (hF_eq n (y : D) y.2).symm
  let T : ℕ → Set U := fun n => {z | (z : ℂ) ∈ interior (K n)}
  have hTopen : ∀ n, IsOpen (T n) := by
    intro n
    exact (isOpen_interior (s := K n)).preimage continuous_subtype_val
  have hTcover : (⋃ n, T n) = Set.univ := by
    ext z
    constructor
    · intro _; exact Set.mem_univ z
    · intro _; exact Set.mem_iUnion.mpr (zex z)
  have hGcont : Continuous G := by
    refine continuous_of_continuousOn_iUnion_of_isOpen (s := T) ?_ hTopen hTcover
    intro n
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : T n => (⟨(z : ℂ), z.2⟩ : interior (K n))) :=
      (continuous_subtype_val.comp continuous_subtype_val :
        Continuous (fun z : T n => (z : ℂ))).subtype_mk (fun z => z.2)
    have hcc : Continuous (fun z : T n =>
        (↑((h n).symm (⟨(z : ℂ), z.2⟩ : interior (K n))) : ℂ)) :=
      (((h n).symm).continuous.comp hc).subtype_val
    have hpf : ∀ z : T n,
        (((h n).symm (⟨(z : ℂ), z.2⟩ : interior (K n))) : ℂ) ∈ Metric.ball (0 : ℂ) 1 :=
      fun z => lt_of_lt_of_le ((h n).symm (⟨(z : ℂ), z.2⟩ : interior (K n))).2 (hrle n)
    have hcont : Continuous (fun z : T n =>
        (⟨↑((h n).symm (⟨(z : ℂ), z.2⟩ : interior (K n))), hpf z⟩ : D)) :=
      hcc.subtype_mk hpf
    refine hcont.congr (fun z => ?_)
    show (⟨↑((h n).symm (⟨(z : ℂ), z.2⟩ : interior (K n))), hpf z⟩ : D) = G (z : U)
    exact (hG_eq n (z : U) z.2).symm
  exact ⟨Homeomorph.mk { toFun := F, invFun := G, left_inv := hleft, right_inv := hright }
    hFcont hGcont⟩

end Work.Smooth.JordanSeparation
