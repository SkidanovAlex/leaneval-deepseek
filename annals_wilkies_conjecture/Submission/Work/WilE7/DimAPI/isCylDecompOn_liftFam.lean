/-
  WilE7 / DimAPI — lifting a cylindrical decomposition of `cubeC n` to one of `cubeC (n+1)`.

  Given a cylindrical decomposition `C'` of the cube `cubeC n = [-1,1]^n`, the family

    `liftFam n C' = ⋃_{γ ∈ C'} liftCells n γ`

  (three cells over each `γ`: the graphs at the levels `±1` and the open band `(-1,1)`, see
  `Submission/Work/WilE7/DimAPI/LiftCells.lean`) is a cylindrical decomposition of
  `cubeC (n+1) = [-1,1]^{n+1}`, with at most `3 * C'.card` members, and it projects back
  onto `C'` under `Fin.init '' ·`.

  The proof glues the *fibrewise* statement

    `liftFamAux_isCylDecompOn_liftCells : IsCylDecompOn (n+1) (cyl γ) (liftCells n γ)`
    (`γ` a nonempty cell)

  along the decomposition `C'` of the base cube, using the restricted gluing theorem
  `Work.WilE7.DimAPI.cylDecomp_union_restricted` from `cylDecomp_union_restricted.lean`,
  which is stated exactly for a base decomposition of `Fin.init '' A` and the fibres
  `A ∩ {z | Fin.init z ∈ b}`.
-/
import Mathlib
import Submission.Work.WilE7.DimAPI.LiftCells
import Submission.Work.WilE7.DimAPI.cylDecomp_union_restricted
import Submission.Work.WilE7.singleton_cylDecomp

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E

/-! ## The cube and the projection, one dimension up -/

/-- Membership in `cubeC (n+1)`, with the last coordinate split off. -/
theorem liftFamAux_mem_cubeC_succ {n : ℕ} (z : Fin (n+1) → ℝ) :
    z ∈ cubeC (n+1) ↔ Fin.init z ∈ cubeC n ∧ |z (Fin.last n)| ≤ 1 := by
  constructor
  · intro h
    exact ⟨fun i => h (Fin.castSucc i), h (Fin.last n)⟩
  · rintro ⟨h1, h2⟩ i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact h1 j
    · exact h2

/-- Dropping the last coordinate maps `cubeC (n+1)` onto `cubeC n`. -/
theorem liftFamAux_init_image_cubeC (n : ℕ) : Fin.init '' cubeC (n+1) = cubeC n := by
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩
    exact fun i => hz (Fin.castSucc i)
  · intro hx
    refine ⟨Fin.snoc x 0, ?_, Fin.init_snoc _ _⟩
    rw [liftFamAux_mem_cubeC_succ]
    exact ⟨by rw [Fin.init_snoc]; exact hx, by simp⟩

/-! ## The fibre over a single cell -/

/-- A lifted cell over `γ` is nonempty as soon as `γ` is: `Fin.init` maps it onto `γ`. -/
theorem liftFamAux_nonempty_of_mem_liftCells {n : ℕ} {γ : Set (Fin n → ℝ)} (hne : γ.Nonempty)
    {κ : Set (Fin (n+1) → ℝ)} (hκ : κ ∈ liftCells n γ) : κ.Nonempty := by
  have hmem : ∀ x ∈ γ, x ∈ Fin.init '' κ := fun x hx => by
    rw [finInit_liftCells hne hκ]; exact hx
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z, hz, -⟩ := hmem x hx
  exact ⟨z, hz⟩

/-- **The fibre over a cell.**  Over a nonempty cell `γ ⊆ ℝⁿ`, the three lifted cells form a
cylindrical decomposition of the cylinder `{z | Fin.init z ∈ γ ∧ |z (Fin.last n)| ≤ 1}`. -/
theorem liftFamAux_isCylDecompOn_liftCells {n : ℕ} {γ : Set (Fin n → ℝ)}
    (hγ : IsCell n γ) (hne : γ.Nonempty) :
    IsCylDecompOn (n+1)
      {z : Fin (n+1) → ℝ | Fin.init z ∈ γ ∧ |z (Fin.last n)| ≤ 1} (liftCells n γ) := by
  have hinit : Fin.init '' {z : Fin (n+1) → ℝ | Fin.init z ∈ γ ∧ |z (Fin.last n)| ≤ 1} = γ := by
    ext x; constructor
    · rintro ⟨z, hz, rfl⟩; exact hz.1
    · intro hx; exact ⟨Fin.snoc x 0, ⟨by simpa using hx, by simp⟩, Fin.init_snoc _ _⟩
  have himg : (liftCells n γ).image (fun κ => Fin.init '' κ) = {γ} := by
    ext κ; constructor
    · intro h
      rw [Finset.mem_image] at h
      obtain ⟨c, hc, rfl⟩ := h
      rw [Finset.mem_singleton]
      exact finInit_liftCells hne hc
    · intro h
      rw [Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_image.mpr ⟨_, mem_liftCells.mpr (Or.inl rfl),
        finInit_liftCells hne (mem_liftCells.mpr (Or.inl rfl))⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro κ hκ
    exact ⟨isCell_liftCells hγ hκ, liftFamAux_nonempty_of_mem_liftCells hne hκ⟩
  · intro κ₁ h₁ κ₂ h₂ h12
    rw [Finset.mem_coe] at h₁ h₂
    rw [mem_liftCells] at h₁ h₂
    rcases h₁ with rfl|rfl|rfl <;> rcases h₂ with rfl|rfl|rfl <;>
      first
        | (exfalso; exact h12 rfl)
        | (refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
           obtain ⟨-, h1⟩ := hz₁
           obtain ⟨-, h2⟩ := hz₂
           linarith)
  · exact sUnion_liftCells γ
  · rw [hinit, himg]
    exact singleton_cylDecomp.1 γ hγ hne

/-! ## The gluing data for `cylDecomp_union_restricted` -/

/-- Every member of a lifted family over `γ ⊆ cubeC n` is contained in `cubeC (n+1)`. -/
theorem liftFamAux_liftCells_subset_cubeC {n : ℕ} {γ : Set (Fin n → ℝ)} (hγ : γ ⊆ cubeC n)
    {κ : Set (Fin (n+1) → ℝ)} (hκ : κ ∈ liftCells n γ) : κ ⊆ cubeC (n+1) := by
  intro z hz
  rw [liftFamAux_mem_cubeC_succ]
  rw [mem_liftCells] at hκ
  rcases hκ with rfl | rfl | rfl
  · exact ⟨hγ hz.1, by rw [hz.2]; norm_num⟩
  · exact ⟨hγ hz.1, abs_le.mpr ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩⟩
  · exact ⟨hγ hz.1, by rw [hz.2]; norm_num⟩

/-- For `b ⊆ cubeC n` the fibre of `cubeC (n+1)` over `b` is the cylinder over `b`. -/
theorem liftFamAux_cubeC_inter_fiber {n : ℕ} {b : Set (Fin n → ℝ)} (hb : b ⊆ cubeC n) :
    cubeC (n+1) ∩ {z : Fin (n+1) → ℝ | Fin.init z ∈ b}
      = {z : Fin (n+1) → ℝ | Fin.init z ∈ b ∧ |z (Fin.last n)| ≤ 1} := by
  ext z; constructor
  · rintro ⟨hzc, hzb⟩
    exact ⟨hzb, ((liftFamAux_mem_cubeC_succ z).mp hzc).2⟩
  · rintro ⟨hzb, hzl⟩
    exact ⟨(liftFamAux_mem_cubeC_succ z).mpr ⟨hb hzb, hzl⟩, hzb⟩

/-- Every member of a cylindrical decomposition is a cell. -/
theorem liftFamAux_isCell_of_mem : ∀ {n : ℕ} {A : Set (Fin n → ℝ)}
    {C : Finset (Set (Fin n → ℝ))}, IsCylDecompOn n A C → ∀ c ∈ C, IsCell n c := by
  intro n
  induction n with
  | zero =>
      intro A C h c hc
      rcases h with ⟨-, hC⟩ | ⟨-, hC⟩
      · subst hC
        rw [Finset.mem_singleton] at hc
        subst hc
        exact IsCell.zero
      · subst hC
        exact absurd hc (Finset.notMem_empty c)
  | succ n ih => intro A C h c hc; exact (h.1 c hc).1

/-! ## The family-level bookkeeping -/

/-- The lifted family projects back onto the base family. -/
theorem liftFamAux_image_liftFam {n : ℕ} {C : Finset (Set (Fin n → ℝ))}
    (hne : ∀ γ ∈ C, γ.Nonempty) :
    (liftFam n C).image (fun κ => Fin.init '' κ) = C := by
  ext γ; constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨κ, hκ, rfl⟩ := h
    rw [mem_liftFam] at hκ
    obtain ⟨γ₀, hγ₀, hκ⟩ := hκ
    rw [finInit_liftCells (hne γ₀ hγ₀) hκ]
    exact hγ₀
  · intro hγ
    refine Finset.mem_image.mpr
      ⟨{y : Fin (n+1) → ℝ | Fin.init y ∈ γ ∧ y (Fin.last n) = -1}, ?_, ?_⟩
    · rw [mem_liftFam]; exact ⟨γ, hγ, mem_liftCells.mpr (Or.inl rfl)⟩
    · exact finInit_liftCells (hne γ hγ) (mem_liftCells.mpr (Or.inl rfl))

/-- The lifted family has at most three members per member of the base family. -/
theorem liftFamAux_card_le {n : ℕ} (C : Finset (Set (Fin n → ℝ))) :
    (liftFam n C).card ≤ 3 * C.card := by
  rw [liftFam]
  calc (C.biUnion (liftCells n)).card ≤ ∑ b ∈ C, (liftCells n b).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ C, 3 := Finset.sum_le_sum fun b _ => Finset.card_le_three
    _ = 3 * C.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-! ## The main statement -/

theorem isCylDecompOn_liftFam {n : ℕ} {C' : Finset (Set (Fin n → ℝ))}
    (hC' : WilkiesDesign.E.IsCylDecompOn n (WilkiesDesign.E.cubeC n) C') :
    WilkiesDesign.E.IsCylDecompOn (n + 1) (WilkiesDesign.E.cubeC (n + 1))
      (Work.WilE7.DimAPI.liftFam n C') ∧
      (Work.WilE7.DimAPI.liftFam n C').card ≤ 3 * C'.card ∧
      (Work.WilE7.DimAPI.liftFam n C').image (fun κ => Fin.init '' κ) = C' := by
  have hsubC : ∀ γ ∈ C', γ ⊆ cubeC n := isCylDecompOn_subset hC'
  have hneC : ∀ γ ∈ C', γ.Nonempty := isCylDecompOn_nonempty hC'
  have hcellC : ∀ γ ∈ C', IsCell n γ := liftFamAux_isCell_of_mem hC'
  have hB : IsCylDecompOn n (Fin.init '' (cubeC (n+1))) C' := by
    rw [liftFamAux_init_image_cubeC]; exact hC'
  have hne : ∀ b ∈ C', (liftCells n b).Nonempty := fun b _ =>
    ⟨_, mem_liftCells.mpr (Or.inl rfl)⟩
  have hsub : ∀ b ∈ C', ∀ κ ∈ liftCells n b, κ ⊆ cubeC (n+1) :=
    fun b hb κ hκ => liftFamAux_liftCells_subset_cubeC (hsubC b hb) hκ
  have hproj : ∀ b ∈ C', ∀ κ ∈ liftCells n b, Fin.init '' κ = b :=
    fun b hb κ hκ => finInit_liftCells (hneC b hb) hκ
  have hB' : ∀ b ∈ C', IsCylDecompOn (n+1)
      (cubeC (n+1) ∩ {z : Fin (n+1) → ℝ | Fin.init z ∈ b}) (liftCells n b) := by
    intro b hb
    rw [liftFamAux_cubeC_inter_fiber (hsubC b hb)]
    exact liftFamAux_isCylDecompOn_liftCells (hcellC b hb) (hneC b hb)
  refine ⟨?_, ?_, ?_⟩
  · exact cylDecomp_union_restricted (cubeC (n+1)) C' (liftCells n) hB hne hsub hproj hB'
  · exact liftFamAux_card_le C'
  · exact liftFamAux_image_liftFam hneC

end Work.WilE7.DimAPI
