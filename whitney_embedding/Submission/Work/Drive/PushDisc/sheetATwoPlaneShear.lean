import Mathlib
import Submission.Work.Drive.PushDisc.localFraming

/-!
# The two-plane framing of the finger: an elementary shear fixes `sheetA` and both double points

`Work.Drive.PushDisc.exists_linearEquiv_fixing_sheetASub` settles the framing at **one** double point:
for a plane `T` transverse to the model first sheet `sheetA` there is a linear isomorphism of the model
space which is the identity on `sheetA` and makes `T` transverse to `kerXV k`.  For the Whitney chart
we need **two** planes at once — the tangent planes of the finger at the two double points `p₂`, `q₂`.

The *pointwise* fixing of `sheetA` used there is too rigid for two planes at once.  With `k = 2` and
`T = span{∂y + ∂u₁, ∂v₁, ∂v₂}` (which *is* transverse to `sheetA`), any linear `L` with
`L|sheetA = id` acts as `(s,n) ↦ s + L' n` on `sheetA ⊕ kerXU k`, so the elements of `L T` lying in
`kerXV k` are the `(f n) + n` with `n ∈ kerXU k` and the `v`-component of `n + L' n` vanishing — a
non-trivial kernel exists because `dim (kerXU k) = k + 1 > k`; hence **no** such `L` works.  The
statement `Work.PushDisc.linearFixTwoPlanes` (pointwise fixing of `sheetA`) is therefore **false**.

The correct statement — and the one the chart construction consumes — keeps `sheetA` invariant only
*setwise* (the first sheet must stay flat, its points may be permuted) and keeps the two model double
points `(±1, 0, 0, 0)` pointwise.  The freedom is then exactly the elementary shear

    L_c (x, y, u, v) = (x + c y, y, u, v),

which fixes `sheetA` pointwise, fixes the two double points, and is a global linear isomorphism.  A
suitable `c` always exists and is found elementarily.  Writing `L_c t = t + (c · t.y) ∂x` and using
the complement `kerXU k = {x = 0, u = 0}` of `sheetA`:

* for a plane `T` transverse to `sheetA` the map `T → kerXU k`, `t ↦ (0, t.y, 0, t.v)` is bijective,
  so there is a unique `t₀(T) ∈ T` with `t₀(T).y = 1` and `t₀(T).v = 0` (`line_of_vanishing_v`);
* the elements `t ∈ T` whose `v`-coordinate vanishes are exactly the multiples of `t₀(T)`;
* `L_c t ∈ kerXV k` for such a `t = a · t₀(T)` means `a · (t₀(T).x + c) = 0`, so `L_c T ∩ kerXV k = 0`
  precisely when `c ≠ -t₀(T).x`.

Hence one `c` avoiding the two numbers `-t₀(T₁).x`, `-t₀(T₂).x` — e.g. any
`c > |t₀(T₁).x| + |t₀(T₂).x|` — does the job for both planes at once.

Main results:

* `finrank_kerXU` — the complement `kerXU k = {x = 0, u = 0}` of `sheetA` has dimension `k + 1`;
* `line_of_vanishing_v` — the line of `T` with vanishing `v`-coordinate;
* `exists_shear_transverse_two_planes` — the shear form;
* `exists_linearEquiv_sheetA_two_planes` — the `≃ₗ` form consumed by the chart.
-/

namespace Work.Drive.PushDisc

open Set

variable {k : ℕ}

/-- The complement `{x = 0, u = 0} = span{∂y, ∂v}` of the model first sheet `sheetA`. -/
def kerXU (k : ℕ) : Submodule ℝ (Work.Drive.Whitney.Mdl k) where
  carrier := {ξ | ξ.1 = 0 ∧ ξ.2.2.1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  smul_mem' c x hx := ⟨by simp [hx.1], by simp [hx.2]⟩

theorem mem_kerXU {ξ : Work.Drive.Whitney.Mdl k} :
    ξ ∈ kerXU k ↔ ξ.1 = 0 ∧ ξ.2.2.1 = 0 := Iff.rfl

/-- The `(x,u)`-coordinates of the model space, whose kernel is `kerXU k`. -/
def coordsXU (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] (ℝ × EuclideanSpace ℝ (Fin k)) where
  toFun ξ := (ξ.1, ξ.2.2.1)
  map_add' x y := rfl
  map_smul' c x := rfl

/-- `kerXU k` has dimension `k + 1` (it is `ℝ × ℝ^k` in the coordinates `(y,v)`). -/
theorem finrank_kerXU (k : ℕ) : Module.finrank ℝ (kerXU k) = k + 1 := by
  have hker : kerXU k = LinearMap.ker (coordsXU k) := by
    ext ξ
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      show (ξ.1, ξ.2.2.1) = (0 : ℝ × EuclideanSpace ℝ (Fin k))
      rw [h1, h2]
      rfl
    · intro h
      have h1 : ξ.1 = 0 := by
        have := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin k) => z.1) h
        simpa [coordsXU] using this
      have h2 : ξ.2.2.1 = 0 := by
        have := congrArg (fun z : ℝ × EuclideanSpace ℝ (Fin k) => z.2) h
        simpa [coordsXU] using this
      exact ⟨h1, h2⟩
  have hrange : LinearMap.range (coordsXU k) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, w⟩
    exact ⟨(a, 0, w, 0), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker (coordsXU k)
  rw [hrange, finrank_top, finrank_Mdl, Module.finrank_prod, finrank_euclideanSpace,
    Fintype.card_fin, Module.finrank_self] at h
  rw [hker]
  omega

/-- The `sheetA`-component `(x, 0, u, 0)` of a model point. -/
def coordsS (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun ξ := (ξ.1, 0, ξ.2.2.1, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- The `kerXU k`-component `(0, y, 0, v)` of a model point. -/
def coordsN (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun ξ := (0, ξ.2.1, 0, ξ.2.2.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

theorem coordsS_mem (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) : coordsS k ξ ∈ sheetASub k :=
  ⟨rfl, rfl⟩

theorem coordsN_mem (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) : coordsN k ξ ∈ kerXU k :=
  ⟨rfl, rfl⟩

theorem coordsS_add_coordsN (k : ℕ) (ξ : Work.Drive.Whitney.Mdl k) :
    coordsS k ξ + coordsN k ξ = ξ := by
  ext <;> simp [coordsS, coordsN]

theorem coordsN_apply (ξ : Work.Drive.Whitney.Mdl k) :
    coordsN k ξ = (0, ξ.2.1, 0, ξ.2.2.2) := rfl

/-- `coordsN` vanishes exactly on the first sheet. -/
theorem coordsN_eq_zero_iff {ξ : Work.Drive.Whitney.Mdl k} :
    coordsN k ξ = 0 ↔ ξ ∈ sheetASub k := by
  constructor
  · intro h
    have h1 : ξ.2.1 = 0 := by
      have := congrArg (fun z : Work.Drive.Whitney.Mdl k => z.2.1) h
      simpa [coordsN] using this
    have h2 : ξ.2.2.2 = 0 := by
      have := congrArg (fun z : Work.Drive.Whitney.Mdl k => z.2.2.2) h
      simpa [coordsN] using this
    exact ⟨h1, h2⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    show (0, ξ.2.1, 0, ξ.2.2.2) = (0 : Work.Drive.Whitney.Mdl k)
    rw [h1, h2]
    rfl

/-- The `y`-coordinate functional of the model space. -/
def coordY (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] ℝ where
  toFun ξ := ξ.2.1
  map_add' x y := rfl
  map_smul' c x := rfl

/-- The first basis vector `∂x` of the model space, as a linear map `ℝ → Mdl k`. -/
def exVec (k : ℕ) : ℝ →ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun a := a • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
  map_add' a b := by
    show (a + b) • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
      = a • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
        + b • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
    rw [add_smul]
  map_smul' a b := by
    show (a * b) • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k)
      = a • (b • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k))
    rw [mul_smul]

/-- **The elementary shear** `(x, y, u, v) ↦ (x + c y, y, u, v)` of the model space.  It fixes
`sheetA` pointwise, hence the two model double points. -/
def shear (k : ℕ) (c : ℝ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] Work.Drive.Whitney.Mdl k :=
  LinearMap.id + (exVec k).comp ((c : ℝ) • coordY k)

theorem shear_apply (c : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    shear k c ξ = ξ + (c * ξ.2.1) • ((1, 0, 0, 0) : Work.Drive.Whitney.Mdl k) := rfl

theorem shear_fst (c : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    (shear k c ξ).1 = ξ.1 + c * ξ.2.1 := by
  rw [shear_apply]
  simp

theorem shear_snd_fst (c : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    (shear k c ξ).2.1 = ξ.2.1 := by
  rw [shear_apply]
  simp

theorem shear_snd_snd_snd (c : ℝ) (ξ : Work.Drive.Whitney.Mdl k) :
    (shear k c ξ).2.2.2 = ξ.2.2.2 := by
  rw [shear_apply]
  simp

/-- The shear as a linear equivalence (its inverse is the shear with `-c`). -/
def shearEquiv (k : ℕ) (c : ℝ) : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k where
  toFun := shear k c
  invFun := shear k (-c)
  left_inv ξ := by
    rw [shear_apply, shear_apply]
    ext <;> simp <;> ring
  right_inv ξ := by
    rw [shear_apply, shear_apply]
    ext <;> simp <;> ring
  map_add' := (shear k c).map_add
  map_smul' := (shear k c).map_smul

theorem shear_fixes_sheetA (c : ℝ) {ξ : Work.Drive.Whitney.Mdl k} (hξ : ξ ∈ sheetASub k) :
    shear k c ξ ∈ sheetASub k := by
  obtain ⟨h1, h2⟩ := hξ
  constructor
  · rw [shear_snd_fst]
    exact h1
  · rw [shear_snd_snd_snd]
    exact h2

/-- The projection of the model space onto `kerXU k` along the first sheet `sheetA`. -/
def projN (k : ℕ) : Work.Drive.Whitney.Mdl k →ₗ[ℝ] kerXU k :=
  (coordsN k).codRestrict (kerXU k) (fun ξ => coordsN_mem k ξ)

/-- The restriction of `projN` to a plane. -/
def projNT (k : ℕ) (T : Submodule ℝ (Work.Drive.Whitney.Mdl k)) : T →ₗ[ℝ] kerXU k :=
  (projN k).comp T.subtype

theorem projNT_apply (k : ℕ) (T : Submodule ℝ (Work.Drive.Whitney.Mdl k)) (x : T) :
    ((projNT k T x : kerXU k) : Work.Drive.Whitney.Mdl k)
      = coordsN k (x : Work.Drive.Whitney.Mdl k) := rfl

/-- **Transversality gives a trivial intersection with the first sheet.** -/
theorem inf_sheetASub_eq_bot_of_transverse {T : Submodule ℝ (Work.Drive.Whitney.Mdl k)}
    (hT : Module.finrank ℝ T = k + 1) (hsup : sheetASub k ⊔ T = ⊤) :
    sheetASub k ⊓ T = ⊥ := by
  refine Submodule.finrank_eq_zero.mp ?_
  have h := Submodule.finrank_sup_add_finrank_inf_eq (sheetASub k) T
  rw [hsup, finrank_top, finrank_Mdl, finrank_sheetASub, hT] at h
  omega

/-- **The line of `T` with vanishing `v`-coordinate.**  For a `(k+1)`-plane `T` transverse to the
model first sheet there is `t₀ ∈ T` with `t₀.y = 1` and `t₀.v = 0`; the elements of `T` with
vanishing `v`-coordinate are exactly its multiples. -/
theorem line_of_vanishing_v {T : Submodule ℝ (Work.Drive.Whitney.Mdl k)}
    (hT : Module.finrank ℝ T = k + 1) (hsup : sheetASub k ⊔ T = ⊤) :
    ∃ t₀ ∈ T, t₀.2.1 = 1 ∧ t₀.2.2.2 = 0 ∧
      ∀ t ∈ T, t.2.2.2 = 0 → t = t.2.1 • t₀ := by
  have hTinf := inf_sheetASub_eq_bot_of_transverse hT hsup
  have hinj : Function.Injective (projNT k T) := by
    intro x y hxy
    have hxy' : coordsN k (x : Work.Drive.Whitney.Mdl k)
        = coordsN k (y : Work.Drive.Whitney.Mdl k) := by
      have h := congrArg (fun z : kerXU k => ((z : kerXU k) : Work.Drive.Whitney.Mdl k)) hxy
      rwa [projNT_apply, projNT_apply] at h
    have h0 : coordsN k ((x : Work.Drive.Whitney.Mdl k) - (y : Work.Drive.Whitney.Mdl k)) = 0 := by
      rw [map_sub, hxy', sub_self]
    have hmemS : (x : Work.Drive.Whitney.Mdl k) - (y : Work.Drive.Whitney.Mdl k)
        ∈ sheetASub k := coordsN_eq_zero_iff.mp h0
    have hmemT : (x : Work.Drive.Whitney.Mdl k) - (y : Work.Drive.Whitney.Mdl k) ∈ T :=
      Submodule.sub_mem T x.2 y.2
    have hbot : (x : Work.Drive.Whitney.Mdl k) - (y : Work.Drive.Whitney.Mdl k) = 0 := by
      have hmem : (x : Work.Drive.Whitney.Mdl k) - (y : Work.Drive.Whitney.Mdl k)
          ∈ sheetASub k ⊓ T := ⟨hmemS, hmemT⟩
      rw [hTinf] at hmem
      simpa using hmem
    exact Subtype.ext (sub_eq_zero.mp hbot)
  have hsurj : Function.Surjective (projNT k T) := by
    rw [← LinearMap.range_eq_top]
    refine Submodule.eq_top_of_finrank_eq ?_
    have h := LinearMap.finrank_range_add_finrank_ker (projNT k T)
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero, hT] at h
    rw [finrank_kerXU]
    omega
  obtain ⟨t₀T, ht₀⟩ := hsurj (⟨(0, 1, 0, 0), by exact ⟨rfl, rfl⟩⟩ : kerXU k)
  have ht₀c : coordsN k ((t₀T : T) : Work.Drive.Whitney.Mdl k) = (0, 1, 0, 0) := by
    have h := congrArg (fun z : kerXU k => ((z : kerXU k) : Work.Drive.Whitney.Mdl k)) ht₀
    rwa [projNT_apply] at h
  refine ⟨((t₀T : T) : Work.Drive.Whitney.Mdl k), t₀T.2, ?_, ?_, ?_⟩
  · exact congrArg (fun z : Work.Drive.Whitney.Mdl k => z.2.1) ht₀c
  · exact congrArg (fun z : Work.Drive.Whitney.Mdl k => z.2.2.2) ht₀c
  · intro t htT htv
    have h1 : coordsN k t = (0, t.2.1, 0, 0) := by
      rw [coordsN_apply, htv]
    have hz : coordsN k (t - t.2.1 • ((t₀T : T) : Work.Drive.Whitney.Mdl k)) = 0 := by
      rw [map_sub, map_smul, h1, ht₀c]
      ext <;> simp
    have hmemS : t - t.2.1 • ((t₀T : T) : Work.Drive.Whitney.Mdl k) ∈ sheetASub k :=
      coordsN_eq_zero_iff.mp hz
    have hmemT : t - t.2.1 • ((t₀T : T) : Work.Drive.Whitney.Mdl k) ∈ T :=
      Submodule.sub_mem T htT (Submodule.smul_mem T _ t₀T.2)
    have hzero : t - t.2.1 • ((t₀T : T) : Work.Drive.Whitney.Mdl k) = 0 := by
      have hmem : t - t.2.1 • ((t₀T : T) : Work.Drive.Whitney.Mdl k) ∈ sheetASub k ⊓ T :=
        ⟨hmemS, hmemT⟩
      rw [hTinf] at hmem
      simpa using hmem
    exact sub_eq_zero.mp hzero

/-- **The two-plane framing.**  If the `(k+1)`-planes `T₁`, `T₂` are both transverse to the model
first sheet, then there is `c : ℝ` such that `L_c (T_i) ∩ kerXV k = 0` for `i = 1, 2`, where `L_c` is
the elementary shear. -/
theorem exists_shear_transverse_two_planes
    (T₁ T₂ : Submodule ℝ (Work.Drive.Whitney.Mdl k))
    (hT₁ : Module.finrank ℝ T₁ = k + 1) (hT₂ : Module.finrank ℝ T₂ = k + 1)
    (hsup₁ : sheetASub k ⊔ T₁ = ⊤) (hsup₂ : sheetASub k ⊔ T₂ = ⊤) :
    ∃ c : ℝ, (∀ t ∈ T₁, shear k c t ∈ kerXV k → t = 0) ∧
      (∀ t ∈ T₂, shear k c t ∈ kerXV k → t = 0) := by
  obtain ⟨t₁, ht₁T, ht₁y, ht₁v, hline₁⟩ := line_of_vanishing_v hT₁ hsup₁
  obtain ⟨t₂, ht₂T, ht₂y, ht₂v, hline₂⟩ := line_of_vanishing_v hT₂ hsup₂
  refine ⟨|t₁.1| + |t₂.1| + 1, ?_, ?_⟩
  · intro t htT hQ
    have h1 : t.1 + (|t₁.1| + |t₂.1| + 1) * t.2.1 = 0 := by
      have h := hQ
      rw [mem_kerXV] at h
      rw [shear_fst] at h
      exact h.1
    have h2 : t.2.2.2 = 0 := by
      have h := hQ
      rw [mem_kerXV] at h
      rw [shear_snd_snd_snd] at h
      exact h.2
    have hl := hline₁ t htT h2
    have hx : t.1 = t.2.1 * t₁.1 := by
      have := congrArg (fun z : Work.Drive.Whitney.Mdl k => z.1) hl
      simpa [smul_eq_mul] using this
    have hfac : t.2.1 * (t₁.1 + (|t₁.1| + |t₂.1| + 1)) = 0 := by
      have h3 := h1
      rw [hx] at h3
      have h4 : t.2.1 * (t₁.1 + (|t₁.1| + |t₂.1| + 1))
          = t.2.1 * t₁.1 + (|t₁.1| + |t₂.1| + 1) * t.2.1 := by ring
      rw [h4]
      exact h3
    have hne : t₁.1 + (|t₁.1| + |t₂.1| + 1) ≠ 0 := by
      have hb : -|t₁.1| ≤ t₁.1 := neg_abs_le _
      have hb2 : (0 : ℝ) ≤ |t₂.1| := abs_nonneg _
      linarith
    have hz : t.2.1 = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact h
      · exact absurd h hne
    rw [hl, hz, zero_smul]
  · intro t htT hQ
    have h1 : t.1 + (|t₁.1| + |t₂.1| + 1) * t.2.1 = 0 := by
      have h := hQ
      rw [mem_kerXV] at h
      rw [shear_fst] at h
      exact h.1
    have h2 : t.2.2.2 = 0 := by
      have h := hQ
      rw [mem_kerXV] at h
      rw [shear_snd_snd_snd] at h
      exact h.2
    have hl := hline₂ t htT h2
    have hx : t.1 = t.2.1 * t₂.1 := by
      have := congrArg (fun z : Work.Drive.Whitney.Mdl k => z.1) hl
      simpa [smul_eq_mul] using this
    have hfac : t.2.1 * (t₂.1 + (|t₁.1| + |t₂.1| + 1)) = 0 := by
      have h3 := h1
      rw [hx] at h3
      have h4 : t.2.1 * (t₂.1 + (|t₁.1| + |t₂.1| + 1))
          = t.2.1 * t₂.1 + (|t₁.1| + |t₂.1| + 1) * t.2.1 := by ring
      rw [h4]
      exact h3
    have hne : t₂.1 + (|t₁.1| + |t₂.1| + 1) ≠ 0 := by
      have hb : -|t₂.1| ≤ t₂.1 := neg_abs_le _
      have hb2 : (0 : ℝ) ≤ |t₁.1| := abs_nonneg _
      linarith
    have hz : t.2.1 = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact h
      · exact absurd h hne
    rw [hl, hz, zero_smul]

/-- **The `≃ₗ` form consumed by the chart**: one linear isomorphism of the model space which keeps
`sheetA` invariant, fixes the two model double points `(±1,0,0,0)`, and makes both `T₁` and `T₂`
transverse to `kerXV k` (i.e. graphs over the `(x,v)`-plane). -/
theorem exists_linearEquiv_sheetA_two_planes
    (T₁ T₂ : Submodule ℝ (Work.Drive.Whitney.Mdl k))
    (hT₁ : Module.finrank ℝ T₁ = k + 1) (hT₂ : Module.finrank ℝ T₂ = k + 1)
    (hsup₁ : sheetASub k ⊔ T₁ = ⊤) (hsup₂ : sheetASub k ⊔ T₂ = ⊤) :
    ∃ L : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] Work.Drive.Whitney.Mdl k,
      (∀ a ∈ sheetASub k, L a ∈ sheetASub k) ∧
      L ((1 : ℝ), 0, 0, 0) = ((1 : ℝ), 0, 0, 0) ∧
      L ((-1 : ℝ), 0, 0, 0) = ((-1 : ℝ), 0, 0, 0) ∧
      (∀ t ∈ T₁, L t ∈ kerXV k → t = 0) ∧
      (∀ t ∈ T₂, L t ∈ kerXV k → t = 0) := by
  obtain ⟨c, h₁, h₂⟩ := exists_shear_transverse_two_planes T₁ T₂ hT₁ hT₂ hsup₁ hsup₂
  refine ⟨shearEquiv k c, fun a ha => shear_fixes_sheetA c ha, ?_, ?_, h₁, h₂⟩
  · show shear k c ((1 : ℝ), 0, 0, 0) = ((1 : ℝ), 0, 0, 0)
    rw [shear_apply]
    simp
  · show shear k c ((-1 : ℝ), 0, 0, 0) = ((-1 : ℝ), 0, 0, 0)
    rw [shear_apply]
    simp

end Work.Drive.PushDisc
